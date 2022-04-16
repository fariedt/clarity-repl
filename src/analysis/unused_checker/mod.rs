use crate::analysis::annotation::Annotation;
use crate::analysis::ast_visitor::{traverse, ASTVisitor, TypedVar};
use crate::analysis::{self, AnalysisPass, AnalysisResult};
use crate::clarity::analysis::analysis_db::AnalysisDatabase;
use crate::clarity::analysis::types::ContractAnalysis;
use crate::clarity::diagnostic::{DiagnosableError, Diagnostic, Level};
use crate::clarity::representations::SymbolicExpressionType::*;
use crate::clarity::representations::{Span, TraitDefinition};
use crate::clarity::{ClarityName, SymbolicExpression};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::iter::FromIterator;

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Settings {
    // Strict mode sets all other options to false
    strict: bool,
    // Private functions that are never called
    unused_private: bool,
    // No reads or writes of maps or variables
    unused_storage: bool,
    // Writes to maps or variables but no reads
    unused_writes: bool,
}

#[derive(Debug, Default, Clone, Copy, Serialize, Deserialize)]
pub struct SettingsFile {
    // Strict mode sets all other options to false
    strict: Option<bool>,
    // Private functions that are never called
    unused_private: Option<bool>,
    // No reads or writes of maps or variables
    unused_storage: Option<bool>,
    // Writes to maps or variables but no reads
    unused_writes: Option<bool>,
}

impl Default for Settings {
    fn default() -> Self {
        Self {
            strict: false,
            unused_private: false,
            unused_storage: false,
            unused_writes: false,
        }
    }
}

impl From<SettingsFile> for Settings {
    fn from(from_file: SettingsFile) -> Self {
        if from_file.strict.unwrap_or(false) {
            Settings {
                strict: true,
                unused_private: true,
                unused_storage: true,
                unused_writes: true,
            }
        } else {
            Settings {
                strict: false,
                unused_private: from_file.unused_private.unwrap_or(false),
                unused_storage: from_file.unused_storage.unwrap_or(false),
                unused_writes: from_file.unused_writes.unwrap_or(false),
            }
        }
    }
}

pub struct CheckError;

impl DiagnosableError for CheckError {
    fn message(&self) -> String {
        "Use of potentially unchecked data".to_string()
    }
    fn suggestion(&self) -> Option<String> {
        None
    }
}

#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Hash)]
enum EventType {
    Define,
    Read,
    Write,
    Call,
}

impl fmt::Display for EventType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                EventType::Define => "define",
                EventType::Read => "read",
                EventType::Write => "write",
                EventType::Call => "call",
            }
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Event {
    name: ClarityName,
    expr: SymbolicExpression,
    event: EventType,
}

pub struct UnusedChecker<'a, 'b> {
    db: &'a mut AnalysisDatabase<'b>,
    settings: Settings,
    // Map expression ID to a generated diagnostic
    diagnostics: HashMap<u64, Diagnostic>,
    // Record all private functions defined
    private_funcs: HashMap<&'a ClarityName, &'a Span>,
    // Record of all public/read-only functions
    public_funcs: HashMap<&'a ClarityName, &'a Span>,
    // Record all maps and variables defined
    maps: HashSet<&'a ClarityName>,
    vars: HashSet<&'a ClarityName>,
    // Record all map and variable events (define, read, write)
    data_events: HashMap<&'a ClarityName, Vec<Event>>,
    // Record all function events (define, call)
    call_events: HashMap<&'a ClarityName, Vec<Event>>,
}

impl Span {
    pub fn contains(&self, other: &Self) -> bool {
        let line_range = self.start_line..(self.end_line + 1);

        line_range.contains(&other.start_line) && line_range.contains(&other.end_line)
    }
}

impl<'a, 'b> UnusedChecker<'a, 'b> {
    fn new(db: &'a mut AnalysisDatabase<'b>, settings: Settings) -> UnusedChecker<'a, 'b> {
        Self {
            db,
            settings,
            diagnostics: HashMap::new(),
            private_funcs: HashMap::new(),
            public_funcs: HashMap::new(),
            maps: HashSet::new(),
            vars: HashSet::new(),
            data_events: HashMap::new(),
            call_events: HashMap::new(),
        }
    }

    fn run(mut self, contract_analysis: &'a ContractAnalysis) -> AnalysisResult {
        // TODO: remove
        println!("-------- {}", &contract_analysis.contract_identifier);

        // First traverse the entire AST
        traverse(&mut self, &contract_analysis.expressions);

        self.analyze();

        // TODO: the comments below are incorrect, we don't need to flatten it like check_checker.
        // TODO: figure out the right approach for storing Diagnostics.

        // Collect all of the vecs of diagnostics into a vector
        let mut diagnostics: Vec<Diagnostic> = self.diagnostics.into_values().collect();
        // Order the sets by the span of the error (the first diagnostic)
        diagnostics.sort_by(|a, b| a.spans[0].cmp(&b.spans[0]));
        // Then flatten into one vector
        // Ok(diagnostics.into_iter().flatten().collect())
        Ok(diagnostics.into_iter().collect())
    }

    // called for map-set, map-insert, map-delete
    fn map_write(&mut self, expr: &'a SymbolicExpression, name: &'a ClarityName) {
        self.data_events.get_mut(name).unwrap().push(Event {
            name: name.clone(),
            expr: expr.clone(),
            event: EventType::Write,
        });
    }

    fn analyze(&mut self) {
        if self.settings.unused_private {
            // TODO: move this code into its own function
            let call_events: Vec<Event> = self.call_events.values().flatten().cloned().collect();
            let mut call_tree: HashMap<ClarityName, HashSet<ClarityName>> = HashMap::new();
            let mut final_tree: HashMap<&ClarityName, HashSet<ClarityName>> = HashMap::new();

            // build call tree by comparing function definition and call spans
            // this is just one level
            for event in call_events.iter() {
                if event.event == EventType::Call {
                    for event2 in call_events.iter() {
                        if event2.expr.span.contains(&event.expr.span) && event2.name != event.name
                        {
                            if call_tree.contains_key(&event2.name.clone()) {
                                call_tree
                                    .get_mut(&event2.name.clone())
                                    .unwrap()
                                    .insert(event.name.clone());
                            } else {
                                call_tree.insert(
                                    event2.name.clone(),
                                    HashSet::from([event.name.clone()]),
                                );
                            }
                            break;
                        }
                    }
                }
            }

            // make a proper tree out of `call_tree`, using known public functions are tree roots
            for (&pubfn, _span) in &self.public_funcs {
                let mut insvals: HashSet<ClarityName> = HashSet::new();
                let mut vals: Vec<ClarityName> = Vec::new();
                if let Some(initial) = call_tree.get(pubfn) {
                    for i in initial {
                        insvals.insert(i.clone());
                        vals.push(i.clone());
                    }
                }
                loop {
                    if let Some(called) = vals.pop() {
                        if let Some(v2) = call_tree.get(&called) {
                            for v in v2 {
                                insvals.insert(v.clone());
                                if !insvals.contains(v) {
                                    vals.push(v.clone());
                                }
                            }
                        }
                    } else {
                        break;
                    }
                }
                final_tree.insert(pubfn, HashSet::from(insvals));
            }

            // println!("FINAL TREE: {:#?}", final_tree);

            // remove called private functions from the rest of the analysis
            for (_pubfn, called) in final_tree {
                for call in called {
                    self.private_funcs.remove(&call);
                }
            }

            // find data events inside unused private functions
            for (name, span) in &self.private_funcs {
                for (&name, events) in &self.data_events.clone() {
                    let mut ok_events: Vec<Event> = Vec::new();
                    for event in events {
                        if span.contains(&event.expr.span) && event.event != EventType::Define {
                            self.diagnostics.insert(
                                event.expr.id,
                                Diagnostic {
                                    level: Level::Warning,
                                    message: format!(
                                        "{} for {} is inside unused private function",
                                        event.event, name
                                    ),
                                    spans: vec![event.expr.span.clone()],
                                    suggestion: None,
                                },
                            );
                        } else {
                            ok_events.push(event.clone());
                        }
                    }
                    if events.len() != ok_events.len() {
                        self.data_events.insert(&name, ok_events);
                    }
                }

                let events = self.call_events.get(name).unwrap();
                for event in events {
                    if event.event == EventType::Define {
                        self.diagnostics.insert(
                            event.expr.id,
                            Diagnostic {
                                level: Level::Warning,
                                message: format!("{} is an unused private function", name),
                                spans: vec![event.expr.span.clone()],
                                suggestion: None,
                            },
                        );
                        break;
                    }
                }
            }
        }

        if self.settings.unused_storage {
            self.check_unused();
        }

        if self.settings.unused_writes {
            self.check_writes();
        }
    }

    fn check_unused(&mut self) {
        // if a map or var has a read event associated with it,
        // it's considered in use.
        let mut t_maps: HashSet<&ClarityName> = HashSet::new();
        let mut t_vars: HashSet<&ClarityName> = HashSet::new();

        for name in &self.maps {
            if self
                .data_events
                .get(name)
                .unwrap()
                .into_iter()
                .any(|event| event.event == EventType::Read)
            {
                t_maps.insert(&name);
            }
        }

        for name in &self.vars {
            if self
                .data_events
                .get(name)
                .unwrap()
                .into_iter()
                .any(|event| event.event == EventType::Read)
            {
                t_vars.insert(&name);
            }
        }

        // remove maps and vars with read events
        for name in &t_maps {
            self.maps.remove(name);
            self.data_events.remove(name);
        }

        for name in &t_vars {
            self.vars.remove(name);
            self.data_events.remove(name);
        }

        t_maps.clear();
        t_vars.clear();

        // if a map or var has a define event associated with it (and no writes)
        // it's unused
        for name in &self.maps {
            let events = self.data_events.get(name).unwrap();
            if events.len() == 1 && events[0].event == EventType::Define {
                self.diagnostics.insert(
                    events[0].expr.id,
                    Diagnostic {
                        level: Level::Warning,
                        message: format!("map {} is declared but not used", name),
                        spans: vec![events[0].expr.span.clone()],
                        suggestion: None,
                    },
                );
                t_maps.insert(name);
            }
        }

        for name in &self.vars {
            let events = self.data_events.get(name).unwrap();
            if events.len() == 1 && events[0].event == EventType::Define {
                self.diagnostics.insert(
                    events[0].expr.id,
                    Diagnostic {
                        level: Level::Warning,
                        message: format!("data-var {} is declared but not used", name),
                        spans: vec![events[0].expr.span.clone()],
                        suggestion: None,
                    },
                );
                t_vars.insert(name);
            }
        }

        for name in &t_maps {
            self.maps.remove(name);
            self.data_events.remove(name);
        }

        for name in &t_vars {
            self.vars.remove(name);
            self.data_events.remove(name);
        }
    }

    fn check_writes(&mut self) {
        // if a map or var has write events associated with it, but not reads,
        // it is marked as a dead write
        for name in &self.maps {
            let define_event = self
                .data_events
                .get(name)
                .unwrap()
                .into_iter()
                .find(|&event| event.event == EventType::Define)
                .unwrap();
            if !self
                .data_events
                .get(name)
                .unwrap()
                .into_iter()
                .any(|event| event.event == EventType::Read)
            {
                self.diagnostics.insert(
                    define_event.expr.id,
                    Diagnostic {
                        level: Level::Warning,
                        message: format!("map {} is written to but not read from", name),
                        spans: vec![define_event.expr.span.clone()],
                        suggestion: None,
                    },
                );
                self.data_events.remove(name);
            }
        }

        for name in &self.vars {
            let define_event = self
                .data_events
                .get(name)
                .unwrap()
                .into_iter()
                .find(|&event| event.event == EventType::Define)
                .unwrap();
            if !self
                .data_events
                .get(name)
                .unwrap()
                .into_iter()
                .any(|event| event.event == EventType::Read)
            {
                self.diagnostics.insert(
                    define_event.expr.id,
                    Diagnostic {
                        level: Level::Warning,
                        message: format!("data-var {} is written to, but not read from", name),
                        spans: vec![define_event.expr.span.clone()],
                        suggestion: None,
                    },
                );
                self.data_events.remove(name);
            }
        }
    }
}

impl AnalysisPass for UnusedChecker<'_, '_> {
    fn run_pass(
        contract_analysis: &mut ContractAnalysis,
        analysis_db: &mut AnalysisDatabase,
        _annotations: &Vec<Annotation>,
        settings: &analysis::Settings,
    ) -> AnalysisResult {
        let checker = UnusedChecker::new(analysis_db, settings.unused_checker);
        checker.run(contract_analysis)
    }
}

impl<'a> ASTVisitor<'a> for UnusedChecker<'a, '_> {
    fn visit_define_private(
        &mut self,
        expr: &'a SymbolicExpression,
        name: &'a ClarityName,
        parameters: Option<Vec<TypedVar<'a>>>,
        body: &'a SymbolicExpression,
    ) -> bool {
        self.private_funcs.insert(name, &expr.span);

        self.call_events.insert(
            name,
            vec![Event {
                name: name.clone(),
                expr: expr.clone(),
                event: EventType::Define,
            }],
        );
        true
    }

    fn visit_define_public(
        &mut self,
        expr: &'a SymbolicExpression,
        name: &'a ClarityName,
        parameters: Option<Vec<TypedVar<'a>>>,
        body: &'a SymbolicExpression,
    ) -> bool {
        self.public_funcs.insert(name, &expr.span);

        self.call_events.insert(
            name,
            vec![Event {
                name: name.clone(),
                expr: expr.clone(),
                event: EventType::Define,
            }],
        );
        true
    }

    fn visit_define_read_only(
        &mut self,
        expr: &'a SymbolicExpression,
        name: &'a ClarityName,
        parameters: Option<Vec<TypedVar<'a>>>,
        body: &'a SymbolicExpression,
    ) -> bool {
        self.public_funcs.insert(name, &expr.span);

        self.call_events.insert(
            name,
            vec![Event {
                name: name.clone(),
                expr: expr.clone(),
                event: EventType::Define,
            }],
        );

        true
    }

    fn visit_call_user_defined(
        &mut self,
        expr: &'a SymbolicExpression,
        name: &'a ClarityName,
        args: &'a [SymbolicExpression],
    ) -> bool {
        self.call_events.get_mut(name).unwrap().push(Event {
            name: name.clone(),
            expr: expr.clone(),
            event: EventType::Call,
        });
        true
    }

    fn visit_fold(
        &mut self,
        expr: &'a SymbolicExpression,
        func: &'a ClarityName,
        sequence: &'a SymbolicExpression,
        initial: &'a SymbolicExpression,
    ) -> bool {
        self.call_events.get_mut(func).unwrap().push(Event {
            name: func.clone(),
            expr: expr.clone(),
            event: EventType::Call,
        });
        true
    }

    fn visit_map(
        &mut self,
        expr: &'a SymbolicExpression,
        func: &'a ClarityName,
        sequences: &'a [SymbolicExpression],
    ) -> bool {
        self.call_events.get_mut(func).unwrap().push(Event {
            name: func.clone(),
            expr: expr.clone(),
            event: EventType::Call,
        });
        true
    }

    fn visit_filter(
        &mut self,
        expr: &'a SymbolicExpression,
        func: &'a ClarityName,
        sequence: &'a SymbolicExpression,
    ) -> bool {
        self.call_events.get_mut(func).unwrap().push(Event {
            name: func.clone(),
            expr: expr.clone(),
            event: EventType::Call,
        });
        true
    }

    fn visit_define_data_var(
        &mut self,
        expr: &'a SymbolicExpression,
        name: &'a ClarityName,
        data_type: &'a SymbolicExpression,
        initial: &'a SymbolicExpression,
    ) -> bool {
        self.vars.insert(name);

        self.data_events.insert(
            name,
            vec![Event {
                name: name.clone(),
                expr: expr.clone(),
                event: EventType::Define,
            }],
        );
        true
    }

    fn visit_var_get(&mut self, expr: &'a SymbolicExpression, name: &'a ClarityName) -> bool {
        self.data_events.get_mut(name).unwrap().push(Event {
            name: name.clone(),
            expr: expr.clone(),
            event: EventType::Read,
        });

        true
    }

    fn visit_var_set(
        &mut self,
        expr: &'a SymbolicExpression,
        name: &'a ClarityName,
        value: &'a SymbolicExpression,
    ) -> bool {
        self.data_events.get_mut(name).unwrap().push(Event {
            name: name.clone(),
            expr: expr.clone(),
            event: EventType::Write,
        });
        true
    }

    fn visit_define_map(
        &mut self,
        expr: &'a SymbolicExpression,
        name: &'a ClarityName,
        key_type: &'a SymbolicExpression,
        value_type: &'a SymbolicExpression,
    ) -> bool {
        self.maps.insert(name);

        self.data_events.insert(
            name,
            vec![Event {
                name: name.clone(),
                expr: expr.clone(),
                event: EventType::Define,
            }],
        );
        true
    }

    fn visit_map_get(
        &mut self,
        expr: &'a SymbolicExpression,
        name: &'a ClarityName,
        key: &HashMap<Option<&'a ClarityName>, &'a SymbolicExpression>,
    ) -> bool {
        self.data_events.get_mut(name).unwrap().push(Event {
            name: name.clone(),
            expr: expr.clone(),
            event: EventType::Read,
        });

        true
    }

    fn visit_map_set(
        &mut self,
        expr: &'a SymbolicExpression,
        name: &'a ClarityName,
        key: &HashMap<Option<&'a ClarityName>, &'a SymbolicExpression>,
        value: &HashMap<Option<&'a ClarityName>, &'a SymbolicExpression>,
    ) -> bool {
        self.map_write(&expr, &name);
        true
    }

    fn visit_map_insert(
        &mut self,
        expr: &'a SymbolicExpression,
        name: &'a ClarityName,
        key: &HashMap<Option<&'a ClarityName>, &'a SymbolicExpression>,
        value: &HashMap<Option<&'a ClarityName>, &'a SymbolicExpression>,
    ) -> bool {
        self.map_write(&expr, &name);
        true
    }

    fn visit_map_delete(
        &mut self,
        expr: &'a SymbolicExpression,
        name: &'a ClarityName,
        key: &HashMap<Option<&'a ClarityName>, &'a SymbolicExpression>,
    ) -> bool {
        self.map_write(&expr, &name);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::Pass;
    use crate::repl::session::Session;
    use crate::repl::SessionSettings;

    #[test]
    fn pub1_calls_priv1() {
        let mut settings = SessionSettings::default();
        settings.repl_settings.analysis.passes = vec![Pass::UnusedChecker];
        let snippet = "
;; public 1 calls private 1

(define-private (private-1) true)
(define-private (private-2) true)
(define-private (private-3) true)

(define-public (public-1) (ok (private-1)))

"
        .to_string();
    }
}
