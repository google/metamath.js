include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cafv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ffn.mm"
include "fafvelrn.mm"
include "ralrimiva.mm"
include "jca.mm"
include "crn.mm"
include "wss.mm"
include "simpl.mm"
include "wceq.mm"
include "wrex.mm"
include "afvelrnb0.mm"
include "nfra1.mm"
include "nfv.mm"
include "wi.mm"
include "rsp.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "syl6.mm"
include "rexlimd.mm"
include "sylan9.mm"
include "ssrdv.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem ffnafv
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let vk: setvar k

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint F y
  disjoint k x
  assert |- ( F : A --> B <-> ( F Fn A /\ A. x e. A ( F ''' x ) e. B ) )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    cA
    wfn
    #
    vx
    cv
    #
    cF
    cafv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    @0
    @1
    @5
    cA
    cB
    cF
    ffn
    @0
    @4
    vx
    cA
    cA
    cB
    @2
    cF
    fafvelrn
    ralrimiva
    jca
    @6
    @1
    cF
    crn
    #
    cB
    wss
    @0
    @1
    @5
    simpl
    @6
    vy
    @7
    cB
    @1
    vy
    cv
    #
    @7
    wcel
    @3
    @8
    wceq
    #
    vx
    cA
    wrex
    @5
    @8
    cB
    wcel
    #
    vx
    cA
    @8
    cF
    afvelrnb0
    @5
    @9
    @10
    vx
    cA
    @4
    vx
    cA
    nfra1
    @10
    vx
    nfv
    @5
    @2
    cA
    wcel
    @4
    @9
    @10
    wi
    @4
    vx
    cA
    rsp
    @9
    @4
    @10
    @3
    @8
    cB
    eleq1
    biimpcd
    syl6
    rexlimd
    sylan9
    ssrdv
    cA
    cB
    cF
    df-f
    sylanbrc
    impbii
end
