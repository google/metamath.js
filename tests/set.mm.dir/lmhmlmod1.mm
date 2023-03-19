include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "clmod.mm"
include "cghm.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "lmhmlem.mm"
include "simplld.mm"

theorem lmhmlmod1
  let cS: class S
  let cT: class T
  let cF: class F


  assert |- ( F e. ( S LMHom T ) -> S e. LMod )

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
    cT
    clmod
    wcel
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
    cS
    cT
    cF
    @1
    @0
    @1
    eqid
    @0
    eqid
    lmhmlem
    simplld
end
