PySasp : Generate Python programs from s(ASP) answer set programs
------------------------------------------------------------------

Installation
------------

1. Need to have SWI-Prolog in PATH 
2. Run make on the top level directory
3. Generated executable is pysasp

Usage: 
------
pysasp <input_file>

To save the file, use IO-redirection of bash environment

pysasp <input_file> >  <output_file>

For optimized version:

pysasp <input_file> -o  > < output_file>

For a sample of how input file must be specified, 
see examples/color.lp


Info
----
<input_file> is an Answer Set Program in a particular format
as outlined in the LOPSTR 2019 Paper

"Synthesizing Imperative Programs from Answer Set Programming
Specifications"

Link to full paper: www.utdallas.edu/~gupta/aspsynthesis.pdf

Every program must additionally have the following annotations:
1. A unique main predicate. If the main predicate name is  "query"
   then the s(ASP) program must contain the fact "main(query)."
2. Every variable in the program must be associated with a domain.
   Every domain must be annotated using the domain predicate.
   If the s(ASP) program uses a domain, say "num" then it should
   contain the fact "domain(num)". 


Parser for PySasp is based on the s(ASP) parser. s(ASP) 
is a Predicate Answer Set Programs that produces stable models
without grounding.

s(ASP) itself downloadable from: 
https://sourceforge.net/projects/sasp-system/

Papers describing s(ASP):

"Computing stable models of normal logic programs without grounding"
Link to paper: https://arxiv.org/pdf/1709.00501.pdf

More recent paper on s(ASP):

"Constraint Answer Set Programming without Grounding"

Link to paper: https://arxiv.org/pdf/1804.11162.pdf
