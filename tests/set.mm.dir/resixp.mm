include "wss.mm"
include "cixp.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "cvv.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "resexg.mm"
include "adantl.mm"
include "w3a.mm"
include "simpr.mm"
include "elixp2.mm"
include "sylib.mm"
include "simp2d.mm"
include "simpl.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "simp3d.mm"
include "ssralv.mm"
include "sylc.mm"
include "fvres.mm"
include "eleq1d.mm"
include "ralbiia.mm"
include "sylibr.mm"
include "syl3anbrc.mm"

theorem resixp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F

  disjoint A x
  disjoint B x
  disjoint F x
  assert |- ( ( B C_ A /\ F e. X_ x e. A C ) -> ( F |` B ) e. X_ x e. B C )

  proof
    cB
    cA
    wss
    #
    cF
    vx
    cA
    cC
    cixp
    #
    wcel
    #
    wa
    #
    cF
    cB
    cres
    #
    cvv
    wcel
    #
    @4
    cB
    wfn
    #
    vx
    cv
    #
    @4
    cfv
    #
    cC
    wcel
    #
    vx
    cB
    wral
    #
    @4
    vx
    cB
    cC
    cixp
    wcel
    @2
    @5
    @0
    cF
    cB
    @1
    resexg
    adantl
    @3
    cF
    cA
    wfn
    #
    @0
    @6
    @3
    cF
    cvv
    wcel
    #
    @11
    @7
    cF
    cfv
    #
    cC
    wcel
    #
    vx
    cA
    wral
    #
    @3
    @2
    @12
    @11
    @15
    w3a
    @0
    @2
    simpr
    vx
    cA
    cC
    cF
    elixp2
    sylib
    #
    simp2d
    @0
    @2
    simpl
    #
    cA
    cB
    cF
    fnssres
    syl2anc
    @3
    @14
    vx
    cB
    wral
    #
    @10
    @3
    @0
    @15
    @18
    @17
    @3
    @12
    @11
    @15
    @16
    simp3d
    @14
    vx
    cB
    cA
    ssralv
    sylc
    @9
    @14
    vx
    cB
    @7
    cB
    wcel
    @8
    @13
    cC
    @7
    cB
    cF
    fvres
    eleq1d
    ralbiia
    sylibr
    vx
    cB
    cC
    @4
    elixp2
    syl3anbrc
end
