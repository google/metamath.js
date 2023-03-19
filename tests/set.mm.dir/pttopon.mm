include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "ctop.mm"
include "cixp.mm"
include "cuni.mm"
include "wceq.mm"
include "cmpt.mm"
include "wf.mm"
include "topontop.mm"
include "ralimi.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylib.mm"
include "cpt.mm"
include "pttop.mm"
include "syl5eqel.mm"
include "sylan2.mm"
include "toponuni.mm"
include "ixpeq2.mm"
include "syl.mm"
include "adantl.mm"
include "ptunimpt.mm"
include "eqtrd.mm"
include "istopon.mm"
include "sylanbrc.mm"

theorem pttopon
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cJ: class J
  let cK: class K
  let cV: class V
  let vy: setvar y
  assume ptunimpt.j: |- J = ( Xt_ ` ( x e. A |-> K ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint K y
  disjoint V y
  assert |- ( ( A e. V /\ A. x e. A K e. ( TopOn ` B ) ) -> J e. ( TopOn ` X_ x e. A B ) )

  proof
    cA
    cV
    wcel
    #
    cK
    cB
    ctopon
    cfv
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    cJ
    ctop
    wcel
    #
    vx
    cA
    cB
    cixp
    #
    cJ
    cuni
    #
    wceq
    cJ
    @5
    ctopon
    cfv
    wcel
    @2
    @0
    cA
    ctop
    vx
    cA
    cK
    cmpt
    #
    wf
    #
    @4
    @2
    cK
    ctop
    wcel
    #
    vx
    cA
    wral
    #
    @8
    @1
    @9
    vx
    cA
    cB
    cK
    topontop
    ralimi
    #
    vx
    cA
    ctop
    cK
    @7
    @7
    eqid
    fmpt
    sylib
    @0
    @8
    wa
    cJ
    @7
    cpt
    cfv
    ctop
    ptunimpt.j
    cA
    @7
    cV
    pttop
    syl5eqel
    sylan2
    @3
    @5
    vx
    cA
    cK
    cuni
    #
    cixp
    #
    @6
    @2
    @5
    @13
    wceq
    #
    @0
    @2
    cB
    @12
    wceq
    #
    vx
    cA
    wral
    @14
    @1
    @15
    vx
    cA
    cB
    cK
    toponuni
    ralimi
    vx
    cA
    cB
    @12
    ixpeq2
    syl
    adantl
    @2
    @0
    @10
    @13
    @6
    wceq
    @11
    vx
    cA
    cJ
    cK
    cV
    ptunimpt.j
    ptunimpt
    sylan2
    eqtrd
    @5
    cJ
    istopon
    sylanbrc
end
