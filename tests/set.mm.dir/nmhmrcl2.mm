include "cnmhm.mm"
include "co.mm"
include "wcel.mm"
include "cnlm.mm"
include "wa.mm"
include "clmhm.mm"
include "cnghm.mm"
include "isnmhm.mm"
include "simplbi.mm"
include "simprd.mm"

theorem nmhmrcl2
  let cS: class S
  let cT: class T
  let cF: class F
  let vs: setvar s
  let vt: setvar t


  assert |- ( F e. ( S NMHom T ) -> T e. NrmMod )

  proof
    cF
    cS
    cT
    cnmhm
    co
    wcel
    #
    cS
    cnlm
    wcel
    #
    cT
    cnlm
    wcel
    #
    @0
    @1
    @2
    wa
    cF
    cS
    cT
    clmhm
    co
    wcel
    cF
    cS
    cT
    cnghm
    co
    wcel
    wa
    cS
    cT
    cF
    isnmhm
    simplbi
    simprd
end
