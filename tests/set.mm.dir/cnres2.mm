include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "ccn.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "cres.mm"
include "crest.mm"
include "simp3l.mm"
include "simp2l.mm"
include "cnrest.mm"
include "syl2anc.mm"
include "ctopon.mm"
include "crn.mm"
include "wb.mm"
include "simp1r.mm"
include "toptopon.mm"
include "sylib.mm"
include "cima.mm"
include "df-ima.mm"
include "simp3r.mm"
include "wfun.mm"
include "cdm.mm"
include "wf.mm"
include "cnf.mm"
include "ffun.mm"
include "3syl.mm"
include "wceq.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "mpbird.mm"
include "syl5eqssr.mm"
include "simp2r.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem cnres2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  assume cnres2.1: |- X = U. J
  assume cnres2.2: |- Y = U. K

  disjoint J x
  disjoint K x
  disjoint F x
  disjoint X x
  disjoint Y x
  disjoint A x
  disjoint B x
  assert |- ( ( ( J e. Top /\ K e. Top ) /\ ( A C_ X /\ B C_ Y ) /\ ( F e. ( J Cn K ) /\ A. x e. A ( F ` x ) e. B ) ) -> ( F |` A ) e. ( ( J |`t A ) Cn ( K |`t B ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    wa
    #
    cA
    cX
    wss
    #
    cB
    cY
    wss
    #
    wa
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    vx
    cv
    cF
    cfv
    cB
    wcel
    vx
    cA
    wral
    #
    wa
    #
    w3a
    #
    cF
    cA
    cres
    #
    cJ
    cA
    crest
    co
    #
    cK
    ccn
    co
    wcel
    #
    @10
    @11
    cK
    cB
    crest
    co
    ccn
    co
    wcel
    #
    @9
    @6
    @3
    @12
    @2
    @5
    @6
    @7
    simp3l
    #
    @2
    @3
    @4
    @8
    simp2l
    #
    cA
    cF
    cJ
    cK
    cX
    cnres2.1
    cnrest
    syl2anc
    @9
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @10
    crn
    #
    cB
    wss
    @4
    @12
    @13
    wb
    @9
    @1
    @16
    @0
    @1
    @5
    @8
    simp1r
    cK
    cY
    cnres2.2
    toptopon
    sylib
    @9
    @17
    cF
    cA
    cima
    #
    cB
    cF
    cA
    df-ima
    @9
    @18
    cB
    wss
    #
    @7
    @2
    @5
    @6
    @7
    simp3r
    @9
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wss
    @19
    @7
    wb
    @9
    @6
    cX
    cY
    cF
    wf
    #
    @20
    @14
    cF
    cJ
    cK
    cX
    cY
    cnres2.1
    cnres2.2
    cnf
    #
    cX
    cY
    cF
    ffun
    3syl
    @9
    cA
    cX
    @21
    @15
    @9
    @6
    @22
    @21
    cX
    wceq
    @14
    @23
    cX
    cY
    cF
    fdm
    3syl
    sseqtr4d
    vx
    cA
    cB
    cF
    funimass4
    syl2anc
    mpbird
    syl5eqssr
    @2
    @3
    @4
    @8
    simp2r
    cB
    @10
    @11
    cK
    cY
    cnrest2
    syl3anc
    mpbid
end
