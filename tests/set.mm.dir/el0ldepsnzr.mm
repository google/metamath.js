include "clmod.mm"
include "wcel.mm"
include "c1.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "chash.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cpw.mm"
include "cnzr.mm"
include "c0g.mm"
include "clindeps.mm"
include "w3a.mm"
include "simp1l.mm"
include "crg.mm"
include "eqid.mm"
include "isnzr2hash.mm"
include "simprbi.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "jca.mm"
include "el0ldep.mm"
include "syld3an1.mm"

theorem el0ldepsnzr
  let cS: class S
  let cM: class M
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( M e. LMod /\ ( Scalar ` M ) e. NzRing ) /\ S e. ~P ( Base ` M ) /\ ( 0g ` M ) e. S ) -> S linDepS M )

  proof
    cM
    clmod
    wcel
    #
    c1
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    chash
    cfv
    clt
    wbr
    #
    wa
    cS
    cM
    cbs
    cfv
    cpw
    wcel
    #
    @0
    @1
    cnzr
    wcel
    #
    wa
    #
    cM
    c0g
    cfv
    cS
    wcel
    #
    cS
    cM
    clindeps
    wbr
    @6
    @4
    @7
    w3a
    @0
    @3
    @0
    @5
    @4
    @7
    simp1l
    @6
    @4
    @3
    @7
    @5
    @3
    @0
    @5
    @1
    crg
    wcel
    @3
    @2
    @1
    @2
    eqid
    isnzr2hash
    simprbi
    adantl
    3ad2ant1
    jca
    cS
    cM
    el0ldep
    syld3an1
end
