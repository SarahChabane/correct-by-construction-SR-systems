# correct-by-construction-SR-systems
#(**************************************************************************)
#(*                                                                        *)
#(*  Correct By construction Synchronous reactive systems                  *)
#(*  Copyright (C) 2018                                                    *)
#(*  Sarah Chabane               &   Rabea Ameur-Boulifa                   *)
#(*  Limose Laboratory               LTCI-Télécom ParisTech                *)
#(*  Boumerdes-Algeria               LabSoC c/o EURECOM -France            *)
#(**************************************************************************)


The present directory contains a tool for modelling Synchronous reactive systems and proof of 
correctness of the generated models. It includes three files : 

1. The file abstioa.ec contains abstract definitions of input/output automata. 

2. The file SRmodel.ec contains the definition of synchronous reactive models (SR-models), and 
the proof of correctness of SRmodels.

3. The file SRcomposition.ec contains the definition of composition of SR-models and proof of 
corretness of the composition.

The proof of correctness of synchronous reactive systems  is performed using Easycrypt tool. 
Available at : https://github.com/EasyCrypt/easycrypt.git
   
