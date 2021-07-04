-- {-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS --rewriting #-}
-- --confluence-check #-}
-- open import Agda.Builtin.Equality.Rewrite



module SetEnvironments.Core where 

open import Level renaming (zero to lzero ; suc to lsuc)
-------------------------------------------------------
-- Environments
-------------------------------------------------------

-- open import SetCats using (Sets ; Sets^ ; SetTerminal ; [Sets^_,Sets] ; SetFunctors-Terminal ; Sets→0Functors)


open import SetCats 
open import RTEnvironments.Core {lsuc lzero} {lsuc lzero} {lsuc lzero} {[Sets^_,Sets]} {SetFunctors-Terminal} 
  renaming (Env to SetEnv
          ; EnvCat to SetEnvCat
          ; EnvMorph to SetEnvMorph 
          ; EnvTC to SetEnvTC 
          ; EnvFV to SetEnvFV 
          ; Env[_,_] to SetEnv[_,_]
          ; EnvM[_,_] to SetEnvM[_,_]
          ; _∘Env_ to _∘SetEnv_ 
          ; idEnv to idSetEnv
          ; mkIdMorph-eq to mkIdNatTr-eq 
          ; _[_:fv=_] to  _[_:fv=_]Set
          ; _[_:fvs=_] to  _[_:fvs=_]Set
          ; ApplyEnv-FV to ApplySetEnv-FV 
          ; ApplyEnv-TC to ApplySetEnv-TC 
          ; ForgetFVEnv to ForgetFVSetEnv 
          ; _≡FV-ext_ to _≡FV-extSetEnv_ 
          ) public 
