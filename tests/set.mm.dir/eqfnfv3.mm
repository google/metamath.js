include "wfn.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wss.mm"
include "wcel.mm"
include "eqfnfv2.mm"
include "eqss.mm"
include "ancom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "anass.mm"
include "dfss3.mm"
include "r19.26.mm"
include "bitr4i.mm"
include "anbi2i.mm"
include "syl6bb.mm"

theorem eqfnfv3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let wph: wff ph

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint B x
  disjoint ph x
  assert |- ( ( F Fn A /\ G Fn B ) -> ( F = G <-> ( B C_ A /\ A. x e. A ( x e. B /\ ( F ` x ) = ( G ` x ) ) ) ) )

  proof
    cF
    cA
    wfn
    cG
    cB
    wfn
    wa
    cF
    cG
    wceq
    cA
    cB
    wceq
    #
    vx
    cv
    #
    cF
    cfv
    @1
    cG
    cfv
    wceq
    #
    vx
    cA
    wral
    #
    wa
    #
    cB
    cA
    wss
    #
    @1
    cB
    wcel
    #
    @2
    wa
    vx
    cA
    wral
    #
    wa
    #
    vx
    cA
    cB
    cF
    cG
    eqfnfv2
    @4
    @5
    cA
    cB
    wss
    #
    wa
    #
    @3
    wa
    #
    @8
    @0
    @10
    @3
    @0
    @9
    @5
    wa
    @10
    cA
    cB
    eqss
    @9
    @5
    ancom
    bitri
    anbi1i
    @11
    @5
    @9
    @3
    wa
    #
    wa
    @8
    @5
    @9
    @3
    anass
    @12
    @7
    @5
    @12
    @6
    vx
    cA
    wral
    #
    @3
    wa
    @7
    @9
    @13
    @3
    vx
    cA
    cB
    dfss3
    anbi1i
    @6
    @2
    vx
    cA
    r19.26
    bitr4i
    anbi2i
    bitri
    bitri
    syl6bb
end
