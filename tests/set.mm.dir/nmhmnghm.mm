include "cnmhm.mm"
include "co.mm"
include "wcel.mm"
include "clmhm.mm"
include "cnghm.mm"
include "cnlm.mm"
include "wa.mm"
include "isnmhm.mm"
include "simprbi.mm"
include "simprd.mm"

theorem nmhmnghm
  let cS: class S
  let cT: class T
  let cF: class F
  let vs: setvar s
  let vt: setvar t


  assert |- ( F e. ( S NMHom T ) -> F e. ( S NGHom T ) )

  proof
    cF
    cS
    cT
    cnmhm
    co
    wcel
    #
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    @0
    cS
    cnlm
    wcel
    cT
    cnlm
    wcel
    wa
    @1
    @2
    wa
    cS
    cT
    cF
    isnmhm
    simprbi
    simprd
end
