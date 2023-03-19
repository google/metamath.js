include "cnvc.mm"
include "ccvs.mm"
include "cnrnvc.mm"
include "cncvs.mm"
include "elini.mm"

theorem cnncvs
  let cC: class C
  assume cnrnvc.c: |- C = ( ringLMod ` CCfld )


  assert |- C e. ( NrmVec i^i CVec )

  proof
    cC
    cnvc
    ccvs
    cC
    cnrnvc.c
    cnrnvc
    cC
    cnrnvc.c
    cncvs
    elini
end
