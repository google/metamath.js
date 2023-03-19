include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cghm.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "lmhmlem.mm"
include "simplr.mm"
include "syl.mm"

theorem lmhmlmod2
  let cS: class S
  let cT: class T
  let cF: class F


  assert |- ( F e. ( S LMHom T ) -> T e. LMod )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    cS
    clmod
    wcel
    #
    cT
    clmod
    wcel
    #
    wa
    cF
    cS
    cT
    cghm
    co
    wcel
    cT
    csca
    cfv
    #
    cS
    csca
    cfv
    #
    wceq
    wa
    #
    wa
    @1
    cS
    cT
    cF
    @3
    @2
    @3
    eqid
    @2
    eqid
    lmhmlem
    @0
    @1
    @4
    simplr
    syl
end
