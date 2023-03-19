include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmulr.mm"
include "c0g.mm"
include "wne.mm"
include "crab.mm"
include "cdm.mm"
include "cmpt.mm"
include "csupp.mm"
include "wceq.mm"
include "oveq2.mm"
include "simpll1.mm"
include "simpll3.mm"
include "eqid.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "necon3d.mm"
include "ss2rabdv.mm"
include "wf.mm"
include "elmapi.mm"
include "fdm.mm"
include "syl.mm"
include "adantl.mm"
include "rabeq.mm"
include "sseqtr4d.mm"
include "cvv.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "cbvmptv.mm"
include "simpl2.mm"
include "fvexd.mm"
include "ovexd.mm"
include "mptsuppd.mm"
include "wfun.mm"
include "elmapfun.mm"
include "simpr.mm"
include "suppval1.mm"
include "syl3anc.mm"
include "3sstr4d.mm"

theorem rmsuppss
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
  assert |- ( ( ( M e. Ring /\ V e. X /\ C e. R ) /\ A e. ( R ^m V ) ) -> ( ( v e. V |-> ( C ( .r ` M ) ( A ` v ) ) ) supp ( 0g ` M ) ) C_ ( A supp ( 0g ` M ) ) )

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
    cR
    wcel
    #
    w3a
    #
    cA
    cR
    cV
    cmap
    co
    #
    wcel
    #
    wa
    #
    cC
    vw
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
    cM
    c0g
    cfv
    #
    wne
    #
    vw
    cV
    crab
    #
    @8
    @11
    wne
    #
    vw
    cA
    cdm
    #
    crab
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
    @9
    co
    #
    cmpt
    #
    @11
    csupp
    co
    cA
    @11
    csupp
    co
    #
    @6
    @13
    @14
    vw
    cV
    crab
    #
    @16
    @6
    @12
    @14
    vw
    cV
    @6
    @7
    cV
    wcel
    #
    wa
    #
    @8
    @11
    @10
    @11
    @24
    @8
    @11
    wceq
    #
    @10
    @11
    wceq
    @25
    @24
    @10
    cC
    @11
    @9
    co
    #
    @11
    @8
    @11
    cC
    @9
    oveq2
    @24
    @0
    @2
    @26
    @11
    wceq
    @0
    @1
    @2
    @5
    @23
    simpll1
    @0
    @1
    @2
    @5
    @23
    simpll3
    cR
    cM
    @9
    cC
    @11
    rmsuppss.r
    @9
    eqid
    @11
    eqid
    ringrz
    syl2anc
    sylan9eqr
    ex
    necon3d
    ss2rabdv
    @6
    @15
    cV
    wceq
    #
    @16
    @22
    wceq
    @5
    @27
    @3
    @5
    cV
    cR
    cA
    wf
    @27
    cA
    cR
    cV
    elmapi
    cV
    cR
    cA
    fdm
    syl
    adantl
    @14
    vw
    @15
    cV
    rabeq
    syl
    sseqtr4d
    @6
    vw
    cV
    @10
    cvv
    @20
    cX
    cvv
    @11
    vv
    vw
    cV
    @19
    @10
    vv
    vw
    weq
    @18
    @8
    cC
    @9
    @17
    @7
    cA
    fveq2
    oveq2d
    cbvmptv
    @0
    @1
    @2
    @5
    simpl2
    @6
    cM
    c0g
    fvexd
    #
    @24
    cC
    @8
    @9
    ovexd
    mptsuppd
    @6
    cA
    wfun
    #
    @5
    @11
    cvv
    wcel
    @21
    @16
    wceq
    @5
    @29
    @3
    cA
    cR
    cV
    elmapfun
    adantl
    @3
    @5
    simpr
    @28
    vw
    @4
    cvv
    cA
    @11
    suppval1
    syl3anc
    3sstr4d
end
