#!/usr/bin/env python3

import re
import os
import sys

args = sys.argv[1:]

usage = "./Name_validator.py [--interactive]"

interactive = False

if len(args) > 1:
  print(usage)
  exit(2)

if len(args) == 1:
  if args[0] == "--interactive":
    interactive = True
  else:
    print(usage)
    exit(2)


curr_dir = os.path.dirname(os.path.realpath(__file__))
src_dir = f"{curr_dir}/../src"

thm_token = "Theorem|Lemma|Fact|Remark|Corollary|Proposition|Property"
def_token = "Definition|Fixpoint|Inductive|Example"
exists_thm_regex = re.compile(f".*({thm_token}|{def_token})\\s*(([a-z]|[A-Z]|_)([a-z]|[A-Z]|_|-|\\d)+)")
def_name_ignore_regex = re.compile("\\s*\\(\\*\\s*\\@nocheck\\s+name\\s*\\*\\)")


acceptable_upper_case = ["Z","X","WF","H","Rz","Rx"]
camel_case_to_snake_case_regex = re.compile(r'(?<!^)(?=[A-Z])')
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
    acceptable_upper_case_str = ", ".join(map(lambda x: '\"' + x + '\"', acceptable_upper_case))
    return f"Violation found: {self.def_type} \"{self.name}\" should be snake_case and lower case following standard library's convention (except for qualifiers: {acceptable_upper_case_str}. Suggestion: {self.fix_snake_case()} ({self._fmt_file()}:{self.line_no})"
  
  def fix_snake_case(self) -> str:
    snake_split = self.name.replace("-","_").split("_")
    results = list()
    for component in snake_split:
      if component not in acceptable_upper_case:
        component_is_upper = component == component.upper()
        if component_is_upper:
          component = component.lower()
        else:
          component = camel_case_to_snake_case_regex \
                      .sub('_', component) \
                      .lower()
      results.append(component)
    snake_cased_name = "_".join(results)
    assert (self.name != snake_cased_name)
    return snake_cased_name

  def replace_in_all(self, files : list[str], change_to : (str | None) = None):
    for file in files: 
      with open(file, "r") as f:
        content = f.read()
      
      if change_to == None:
        change_to = self.fix_snake_case()
      
      content = content.replace(self.name, change_to)

      with open(file, "w") as f:
        f.write(content)
      
  def ignore(self):
    with open(self.file, "r") as f:
      lines = f.readlines()

    lines.insert(self.line_no - 1, "(* @nocheck name *)\n")

    with open(self.file, "w") as f:
      lines = "".join(lines)
      f.write(lines)
    
acceptable_upper_case_regex = "|".join(acceptable_upper_case)

snake_case_regex = re.compile(f"_?(({acceptable_upper_case_regex}|[a-z]([a-z][0-9])*)_)*({acceptable_upper_case_regex}|[a-z]([a-z][0-9])*)")

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

all_files : list[str] = list()

for dir, _, files in os.walk(src_dir):
    if ".Old" in dir:
      continue
    for file in files:
      if not file.endswith(".v"): # Make sure we only look at Coq files
        continue
      all_files.append(f"{dir}/{file}")
      file_name_violation = check_file_name(file, f"{dir}/{file}")
      if file_name_violation:
        file_name_violations.append(file_name_violation)
      name_violations += validate_file(f"{dir}/{file}")


if not name_violations and not file_name_violations:
  print("No violations found")
  exit(0)

all_violations = file_name_violations + name_violations
n_violations = len(all_violations)



def replaceAll(violation : Violation):
  pass



for (n, violation) in enumerate(all_violations, 1):
  print(f"({n}/{n_violations}) - {violation}")
  if interactive:
    while True:
      option = input("What do you want to do? Auto Fix(F)/Manually Fix(M)/Skip(S)/Ignore(I) permanently? ").lower()
      if option == "f":
        violation.replace_in_all(all_files)
        break
      if option == "m":
        change_to = input('Input desired new name: ')
        violation.replace_in_all(all_files, change_to)
        break
      elif option == "i":
        violation.ignore()
        break
      elif option == "s":
        break
      else:
        print("Invalid option...")


if not interactive:
  print(f"Fix issues by running {os.path.realpath(__file__)} --interactive")
exit(1)