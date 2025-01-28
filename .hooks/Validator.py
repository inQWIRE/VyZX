from pathlib import Path
from __future__ import annotations
from enum import Enum
import re
from typing import Iterator, Optional
from abc import abstractmethod
import os
import colorama # Use this instead of ANSI colors as those break on Windows systems
from functools import reduce, cached_property
from itertools import chain


class CoqDefinitionType(Enum):
  THEOREM = "Theorem"
  LEMMA = "Lemma"
  EXAMPLE = "Example"
  FACT = "Fact"
  REMARK = "Remark"
  PROPERTY = "Property"
  COROLLARY = "Corollary"
  PROPOSITION = "Proposition"
  DEFINITION = "Definition"
  FIXPOINT = "Fixpoint"
  COFIXPOINT = "CoFixpoint"
  INDUCTIVE = "Inductive"
  COINDUCTIVE = "CoInductive"
  RECORD = "Record"
  STRUCTURE = "Structure"
  # TODO: Add Program, which in general will require more work, given the Obligation syntax that we just don't cover atm
  
ALL_DEFS = [def_type.value for def_type in CoqDefinitionType]

Interval = tuple[int, int]

class CheckerType(Enum):
  PROOF_LINES = "Proof Lines"
  DEFS = "Defs"
  ALL = "All"


class FileValidator:
  file : Path
  validator : Validator

  @cached_property
  def get_file_lines(self) -> list[str]:
    # Cache lines to DRY (files are assumed to not be edited at time of check - which is a bad assumption in and LSP context, so we might need to rethink this)
    with open(self.file, 'r') as f:
      return f.readlines()
  
  def get_proof_lines(self, def_type : list[CoqDefinitionType] = ALL_DEFS) -> list[Interval]:
    def_intervals = self.get_definition_lines(def_type)
    proof_end_regex = r"Qed\.|Defined\.|Admitted\.|Abort\."
    # Go through all intervals and go from end+1 until we hit proof_end_regex
    proof_intervals = []
    starts = {start for start, _ in def_intervals}
    for start, end in def_intervals:
      for i in range(end + 1, len(self.get_file_lines())):
        if i in starts:
          break # This can happen in case there is no proof mode definition
        if re.search(proof_end_regex, self.get_file_lines()[i]):
          proof_intervals.append((start, i))
          break
    return proof_intervals
  
  def get_definition_lines(self, def_type: list[CoqDefinitionType] = ALL_DEFS) -> list[Interval]:
    def_start_reg_str = rf"{"|".join(def_type)}"
    complete_def_str = rf"{def_start_reg_str}((?!(Proof.)).|\n|\r)*\." # This isn't perfect in case proofs don't start with Proof, but parsing that would be quite a bit more complicated, since "." can be a module accessor
    lines = self.get_file_lines()
    for i in range(len(lines)):
      # if def start matches keep adding lines until complete def matches, then add interval
      intervals = []
      i = 0
      while i < len(lines):
        if re.match(def_start_reg_str, lines[i]):
          start = i
          while i < len(lines):
            complete_def_cand = "\n".join(lines[start:i+1])
            if re.match(complete_def_str, complete_def_cand):
              break
            i += 1
          if i < len(lines):
            intervals.append((start, i))
        i += 1
      return intervals
  
  def get_next_non_empty_line_up(self, line : int) -> Optional[int]:
    lines = self.get_file_lines()
    for i in range(line - 1, -1, -1):
      if lines[i].strip():
        return i
    return None
  
  def has_no_check_modulo_empty_lines(self, line : int) -> bool:
    last_non_empty_line = self.get_next_non_empty_line_up(line)
    if not last_non_empty_line:
      return False
    return self.has_no_check(last_non_empty_line)
  
  def has_no_check(self, line : int) -> bool:
    line_str = self.get_file_lines()[line]
    return re.match(rf"\s*\(\*\s*nocheck\s+{self.validator.nocheck_tag}\s*\*\)\s*", line_str)
  
  @abstractmethod
  def check(self, regex: re.Pattern, lines: Interval) -> Optional[Violation]:
    pass

  @abstractmethod
  def find_violations(self) -> list[Violation]:
    pass
  
  

class Validator:
  name : str
  nocheck_tag : str
  src_dir : str
  type: CheckerType
  
  def find_all_files(self) -> Iterator[Path]:
    for _, _, files in os.walk(self.src_dir):
      for file in files:
        if not file.endswith(".v"): # Make sure we only look at Coq files
          continue
        yield Path(file)
  
  def find_all_violations(self) -> dict[Path, list[Violation]]:
    return {file: FileValidator(file, self).find_violations() for file in self.find_all_files()}
  
  def find_all_violations_flat(self) -> list[Violation]:
    violations_by_file = self.find_all_violations().values()
    return list(chain.from_iterable(violations_by_file))
    
  def run(self, interactive: bool):
    all_violations = self.find_all_violations_flat()

    if not all_violations:
      print("No violations found")
      return

    num_violations = len(all_violations) # TODO: Do we want to group up all violations together or have them by violation type as we effectively do now?
    
    for (n, violation) in enumerate(all_violations, 1):
      print(f"({n}/{num_violations}) {violation}")
      if not interactive:
        continue
      while True: # Do until a valid input comes along
        option = input(f"What do you want to do? Remove(R)/Skip(S)/Ignore(I) permanently? ").lower()
        if option == "r":
          violation.fix()
          break
        elif option == "i":
          violation.ignore()
          break
        elif option == "s":
          break
        else:
          print("Invalid option...")

      if not interactive:
        print(f"{b_color_green}Fix issues by running {os.path.realpath(__file__)} --interactive{b_color_reset}") # TODO: Change this behavior
  
class Violation:
  lines_no : Optional[int | Interval | list[int]] = None
  file : str = ""
  validator : Validator

  def _fmt_file(self) -> str:
    prefix, _, postfix = self.file.partition(".hooks/../") # strip going into the hooks directory
    # todo: generalize
    abs_path = prefix + postfix
    if not self.lines_no:
      return abs_path
    elif isinstance(self.lines_no, int):
      return f"{abs_path}:{self.lines_no}"
    elif isinstance(self.lines_no, Interval):
      return f"{abs_path}:{self.lines_no[0]}-{self.lines_no[1]}"
    elif isinstance(self.lines_no, list[int]):
      return f"{abs_path}:{",".join(self.lines_no)}"
    else:
      raise ValueError("Line must be an int or an interval or a list of ints (or nothing)")
      

  @abstractmethod
  def fix(self, comment : str):
    pass

  def ignore(self):
    with open(self.file, "r") as f:
      lines = f.readlines()

    lines.insert(self.line_no - 1, f"(* @nocheck {self.validator.nocheck_tag} *)\n")

    with open(self.file, "w") as f:
      lines = "".join(lines)
      f.write(lines)

  @abstractmethod
  def __str__(self) -> str:
    pass
