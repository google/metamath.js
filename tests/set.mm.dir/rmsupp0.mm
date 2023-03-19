include "crg.mm"
include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cmulr.mm"
include "cmpt.mm"
include "csupp.mm"
include "wne.mm"
include "crab.mm"
include "c0.mm"
include "cvv.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "cbvmptv.mm"
include "simpl2.mm"
include "fvexd.mm"
include "ovexd.mm"
include "mptsuppd.mm"
include "simpll3.mm"
include "oveq1d.mm"
include "cbs.mm"
include "simpll1.mm"
include "wi.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "syl6eleq.mm"
include "ex.mm"
include "syl.mm"
include "adantl.mm"
include "imp.mm"
include "eqid.mm"
include "ringlz.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "neeq1d.mm"
include "rabbidva.mm"
include "wn.mm"
include "wral.mm"
include "neirr.mm"
include "a1i.mm"
include "ralrimivw.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "3eqtrd.mm"

theorem rmsupp0
  let vv: setvar v
  let cA: class A
  let cC: class C
  let cR: class R
  let cM: class M
  let cV: class V
  let cX: class X
  let vw: setvar w
  let vk: setvar k
  let vx: setvar x
  assume rmsuppss.r: |- R = ( Base ` M )

  disjoint A v
  disjoint C v
  disjoint M v
  disjoint R v
  disjoint X v
  disjoint V v
  disjoint A w
  disjoint v w
  disjoint C w
  disjoint M w
  disjoint R w
  disjoint X w
  disjoint V w
  disjoint k x
  assert |- ( ( ( M e. Ring /\ V e. X /\ C = ( 0g ` M ) ) /\ A e. ( R ^m V ) ) -> ( ( v e. V |-> ( C ( .r ` M ) ( A ` v ) ) ) supp ( 0g ` M ) ) = (/) )

  proof
    cM
    crg
    wcel
    #
    cV
    cX
    wcel
    #
    cC
    cM
    c0g
    cfv
    #
    wceq
    #
    w3a
    #
    cA
    cR
    cV
    cmap
    co
    wcel
    #
    wa
    #
    vv
    cV
    cC
    vv
    cv
    #
    cA
    cfv
    #
    cM
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    @2
    csupp
    co
    cC
    vw
    cv
    #
    cA
    cfv
    #
    @9
    co
    #
    @2
    wne
    #
    vw
    cV
    crab
    @2
    @2
    wne
    #
    vw
    cV
    crab
    #
    c0
    @6
    vw
    cV
    @14
    cvv
    @11
    cX
    cvv
    @2
    vv
    vw
    cV
    @10
    @14
    vv
    vw
    weq
    @8
    @13
    cC
    @9
    @7
    @12
    cA
    fveq2
    oveq2d
    cbvmptv
    @0
    @1
    @3
    @5
    simpl2
    @6
    cM
    c0g
    fvexd
    @6
    @12
    cV
    wcel
    #
    wa
    #
    cC
    @13
    @9
    ovexd
    mptsuppd
    @6
    @15
    @16
    vw
    cV
    @19
    @14
    @2
    @2
    @19
    @14
    @2
    @13
    @9
    co
    #
    @2
    @19
    cC
    @2
    @13
    @9
    @0
    @1
    @3
    @5
    @18
    simpll3
    oveq1d
    @19
    @0
    @13
    cM
    cbs
    cfv
    #
    wcel
    #
    @20
    @2
    wceq
    @0
    @1
    @3
    @5
    @18
    simpll1
    @6
    @18
    @22
    @5
    @18
    @22
    wi
    #
    @4
    @5
    cV
    cR
    cA
    wf
    #
    @23
    cA
    cR
    cV
    elmapi
    @24
    @18
    @22
    @24
    @18
    wa
    @13
    cR
    @21
    cV
    cR
    @12
    cA
    ffvelrn
    rmsuppss.r
    syl6eleq
    ex
    syl
    adantl
    imp
    @21
    cM
    @9
    @13
    @2
    @21
    eqid
    @9
    eqid
    @2
    eqid
    ringlz
    syl2anc
    eqtrd
    neeq1d
    rabbidva
    @6
    @16
    wn
    #
    vw
    cV
    wral
    @17
    c0
    wceq
    @6
    @25
    vw
    cV
    @25
    @6
    @2
    neirr
    a1i
    ralrimivw
    @16
    vw
    cV
    rabeq0
    sylibr
    3eqtrd
end
