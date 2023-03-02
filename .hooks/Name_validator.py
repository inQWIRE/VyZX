#!/usr/bin/env python3

import re
import os

curr_dir = os.path.dirname(os.path.realpath(__file__))
src_dir = f"{curr_dir}/../src"

thm_token = "Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property"
def_token = "Definition|Fixpoint|Inductive|Example"
exists_thm_regex = re.compile(f".*({thm_token}|{def_token})\\s*(([a-z]|[A-Z]|_)([a-z]|[A-Z]|_|-|\\d)+)")
def_name_ignore_regex = re.compile("\\s*\\(\\*\\s*\\@nocheck\\s+name\\s*\\*\\)")

class Violation:
  line_no : (int | None) 
  file : str = ""
  name : str 
  def_type : (str | None)

  def __init__(self, line_no : (int | None), file : str, name : str, def_type : (str | None)):
    self.file = file
    self.line_no = line_no
    self.name = name
    self.def_type = def_type

  def _fmt_file(self) -> str:
    prefix, _, postfix = self.file.partition(".hooks/../") # strip going into the hooks directory
    return prefix + postfix

  def __str__(self) -> str:
    if (not self.line_no) or (not self.def_type): # File global violation
      return f"Violation found: {self.name} is a disallowed file name. Should be PascalCase (where only the beginning can have multiple uppercase letters in  row) ({self._fmt_file()})"

    return f"Violation found: {self.def_type} \"{self.name}\" should be snake_case and lower case following standard library's convention (except for qualifiers: Z_ X_ Z_X_ X_Z_ WF_). ({self._fmt_file()}:{self.line_no})"
    

snake_case_regex = re.compile("((Z|X|WF|[a-z]([a-z][0-9])*)_)*(Z|X|WF|[a-z]([a-z][0-9])*)")

def validate_file(file) -> list[Violation]:
  violations : list[Violation] = list()
  with open(file) as lines:
    skip_next = False
    for (line_no, line) in enumerate(lines, 1):
      if re.match(def_name_ignore_regex, line):
        skip_next = True
        continue
      match = re.match(exists_thm_regex, line)
      if match:
        if skip_next:
          skip_next = False
          continue
        def_type = match.groups()[0]
        name = match.groups()[1]
        name_matches_rules = re.match(snake_case_regex, name)
        if not name_matches_rules:
          violations.append(Violation(line_no, file, name, def_type))
  return violations


file_name_regex = re.compile("[A-Z]*([A-Z][a-z])+")
file_name_ignore_regex = re.compile("\\s*\\(\\*\\s*\\@nocheck\\s+filename\\s*\\*\\)")

def check_file_name(file_name : str, file_path : str) -> (Violation | None):
  if ".Old" in file_path:
    return None
  with open(file_path) as lines:
    first_line = lines.readline()
    if first_line:
      is_ignored = re.match(file_name_ignore_regex, first_line)
      if is_ignored:
        return None
  if re.match(file_name_regex,file_name):
    return None
  return Violation(None, file_path, file_name, None)
  


print("Checking src/ directory for comforming theorem names...")
name_violations : list[Violation] = list()
file_name_violations: list[Violation] = list()

for dir, _, files in os.walk(src_dir):
    for file in files:
      if not file.endswith(".v"): # Make sure we only look at Coq files
        continue
      file_name_violation = check_file_name(file, f"{dir}/{file}")
      if file_name_violation:
        file_name_violations.append(file_name_violation)
      name_violations += validate_file(f"{dir}/{file}")


if not name_violations and not file_name_violations:
  print("No violations found")
  exit(0)

for violation in file_name_violations + name_violations:
  print(violation)

exit(1)