
module RelEnvironments.EnvironmentExtension where

open import RelSem.RelCats-Set using (Rels ; RTCat ; RT-Terminal ; Rels⇒RT0)

-- open import Environments.EnvironmentExtension (Rels) (RelTerminal) public 

open import RTEnvironments.EnvironmentExtension (Rels) (RTCat) (RT-Terminal) (Rels⇒RT0)
  renaming ( extendTEnv2 to extendTRelEnv
           ; extendEnv2 to extendRelEnv2 
           ; extendEnv-ρ×As to extendRelEnv-ρ×As
           )
           public 


--   (toD0 : Functor R (D 0)) 
