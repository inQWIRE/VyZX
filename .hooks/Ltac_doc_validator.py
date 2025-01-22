#!/usr/bin/env python3

import re
import os
import sys


MIN_PYTHON = (3, 10)
if sys.version_info < MIN_PYTHON:
  print(f"Your python version is {sys.version_info.major}.{sys.version_info.minor}. {MIN_PYTHON[0]}.{MIN_PYTHON[1]} is required")
  exit(3)

args = sys.argv[1:]

usage = "./Name_validator.py [--interactive]"

interactive = False

b_color_green = '\033[92m'
b_color_yellow = '\033[93m'
b_color_reset = '\033[0m'


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
    
comment_length_threshold = 100   
    
class Violation:
  line_no : int = 0
  ltac_name : str
  doc_length : int = 0
  file : str = ""

  def __init__(self, line_no : int, ltac_name: str, file : str, doc_length : int = 0):
    self.file = file
    self.ltac_name = ltac_name
    self.line_no = line_no
    self.doc_length = doc_length

  def _fmt_file(self) -> str:
    prefix, _, postfix = self.file.partition(".hooks/../") # strip going into the hooks directory
    return prefix + postfix
  
  def fix(self, comment : str):
    with open(self.file, "r") as f:
      lines = f.readlines()
    comment_lines= list(map(lambda s: f"(* {s} *)", comment.splitlines()))
    lines = lines[:self.line_no] + comment_lines + lines[self.line_no:]
    with open(self.file, "w") as f:
      lines = "".join(lines)
      f.write(lines)

  def ignore(self):
    with open(self.file, "r") as f:
      lines = f.readlines()

    lines.insert(self.line_no - 1, "(* @nocheck tacdoc *)\n")

    with open(self.file, "w") as f:
      lines = "".join(lines)
      f.write(lines)

  def __str__(self) -> str:
    warning_str = ""
    if self.doc_length > 0:
      warning_str = f"UNDERdocumented tactic \"{self.ltac_name}\" found; comment is only {self.doc_length} chars long, while we require {comment_length_threshold}, which points to insufficient documentation. Please review"
    else: 
      warning_str = f"Undocumented tactic \"{self.ltac_name}\" found"
    return f"{b_color_yellow}Warning: {warning_str}: {b_color_reset}({self._fmt_file()}:{self.line_no})"
    pass


ltac_regex = r'^\s*(Ltac2? (\S+)|Tactic Notation ((\"\S+\"\s*)+))\s+.*:='
comment_regex = r'\(\*(.*)\*\)'
no_check_regex = re.compile("\\s*\\(\\*\\s*\\@nocheck\\s+tacdoc\\s*\\*\\)")

def find_prev_non_empty(lines: list[str], line_no: int) -> int:
  curr_line = line_no -1
  while curr_line >= 0 and lines[curr_line].strip() == "":
    curr_line = curr_line - 1
  return curr_line

def get_all_comments_up(lines: list[str], line_no: int) -> list[str]:
  curr_line = line_no 
  ret = []
  while curr_line >= 0 and \
      (lines[curr_line].strip() == "" or \
       re.match(comment_regex, lines[curr_line])):
      if not lines[curr_line].strip() == "":
        comment = re.match(comment_regex, lines[curr_line])
        ret.append(comment.groups()[0] if comment else lines[curr_line])  
      curr_line = curr_line - 1
  return ret


def validate_file(file) -> list[Violation]:
  warnings : list[Violation] = list()
  with open(file) as f:
    lines = f.readlines()
  
  for (line_no, line) in enumerate(lines):
    ltac_match = re.match(ltac_regex, line)      
    if ltac_match:
      ltac_name = ltac_match.groups()[1] if ltac_match.groups()[1] else ltac_match.groups()[2].replace("\"","")
      no_check_match = re.match(no_check_regex, lines[line_no - 1]) 
      if no_check_match:
        continue
      comments = get_all_comments_up(lines, line_no - 1)
      comment = '\n'.join(comments)
      if len(comment) < comment_length_threshold:
        user_line_no = line_no + 1 # 1 indexing
        warnings.append(Violation(user_line_no, ltac_name, file, len(comment)))
  return warnings


print("Checking src/ directory for any files containing undocumented tactics...")
all_violations : list[Violation] = list()

for dir, _, files in os.walk(src_dir):
    for file in files:
      if not file.endswith(".v"): # Make sure we only look at Coq files
        continue
      all_violations += validate_file(f"{dir}/{file}")


if not all_violations:
  print("No violations found")
  exit(0)

num_violations = len(all_violations)

for (n, violation) in enumerate(all_violations, 1):
  print(f"({n}/{num_violations}) {violation}")
  if not interactive:
    continue
  while True: # Do until a valid input comes along
    option = input(f"What do you want to do? Skip and fix in editor(S)/Ignore(I) permanently? ").lower()
    if option == "i":
      violation.ignore()
      break
    elif option == "s":
      break
    else:
      print("Invalid option...")

if not interactive:
  print(f"{b_color_green}Fix issues by running {os.path.realpath(__file__)} --interactive{b_color_reset}")

exit(1)