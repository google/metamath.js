include "cnmhm.mm"
include "co.mm"
include "wcel.mm"
include "cnghm.mm"
include "cghm.mm"
include "nmhmnghm.mm"
include "nghmghm.mm"
include "syl.mm"

theorem nmhmghm
  let cS: class S
  let cT: class T
  let cF: class F
  let vs: setvar s
  let vt: setvar t


  assert |- ( F e. ( S NMHom T ) -> F e. ( S GrpHom T ) )

  proof
    cF
    cS
    cT
    cnmhm
    co
    wcel
    cF
    cS
    cT
    cnghm
    co
    wcel
    cF
    cS
    cT
    cghm
    co
    wcel
    cS
    cT
    cF
    nmhmnghm
    cS
    cT
    cF
    nghmghm
    syl
end
