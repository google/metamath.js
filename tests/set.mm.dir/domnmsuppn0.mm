include "cdomn.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "cfv.mm"
include "wne.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "cmulr.mm"
include "crab.mm"
include "cdm.mm"
include "cmpt.mm"
include "csupp.mm"
include "wceq.mm"
include "wf.mm"
include "elmapi.mm"
include "fdm.mm"
include "eqcomd.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "oveq2.mm"
include "crg.mm"
include "domnring.mm"
include "adantr.mm"
include "simpl.mm"
include "anim12i.mm"
include "3adant3.mm"
include "eqid.mm"
include "ringrz.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "necon3d.mm"
include "simpl1l.mm"
include "simpll2.mm"
include "wi.mm"
include "ffvelrn.mm"
include "imp.mm"
include "simpr.mm"
include "domnmuln0.mm"
include "syl112anc.mm"
include "impbid.mm"
include "rabeqbidva.mm"
include "cvv.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "cbvmptv.mm"
include "simp1r.mm"
include "fvexd.mm"
include "ovexd.mm"
include "mptsuppd.mm"
include "wfun.mm"
include "elmapfun.mm"
include "simp3.mm"
include "suppval1.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"

theorem domnmsuppn0
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
  assert |- ( ( ( M e. Domn /\ V e. X ) /\ ( C e. R /\ C =/= ( 0g ` M ) ) /\ A e. ( R ^m V ) ) -> ( ( v e. V |-> ( C ( .r ` M ) ( A ` v ) ) ) supp ( 0g ` M ) ) = ( A supp ( 0g ` M ) ) )

  proof
    cM
    cdomn
    wcel
    #
    cV
    cX
    wcel
    #
    wa
    #
    cC
    cR
    wcel
    #
    cC
    cM
    c0g
    cfv
    #
    wne
    #
    wa
    #
    cA
    cR
    cV
    cmap
    co
    #
    wcel
    #
    w3a
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
    @4
    wne
    #
    vw
    cV
    crab
    @11
    @4
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
    @12
    co
    #
    cmpt
    #
    @4
    csupp
    co
    cA
    @4
    csupp
    co
    #
    @9
    @14
    @15
    vw
    cV
    @16
    @8
    @2
    cV
    @16
    wceq
    #
    @6
    @8
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
    #
    @24
    @16
    cV
    cV
    cR
    cA
    fdm
    eqcomd
    syl
    3ad2ant3
    @9
    @10
    cV
    wcel
    #
    wa
    #
    @14
    @15
    @27
    @11
    @4
    @13
    @4
    @27
    @11
    @4
    wceq
    #
    @13
    @4
    wceq
    @28
    @27
    @13
    cC
    @4
    @12
    co
    #
    @4
    @11
    @4
    cC
    @12
    oveq2
    @9
    @29
    @4
    wceq
    #
    @26
    @9
    cM
    crg
    wcel
    #
    @3
    wa
    #
    @30
    @2
    @6
    @32
    @8
    @2
    @31
    @6
    @3
    @0
    @31
    @1
    cM
    domnring
    adantr
    @3
    @5
    simpl
    anim12i
    3adant3
    cR
    cM
    @12
    cC
    @4
    rmsuppss.r
    @12
    eqid
    #
    @4
    eqid
    #
    ringrz
    syl
    adantr
    sylan9eqr
    ex
    necon3d
    @27
    @15
    @14
    @27
    @15
    wa
    @0
    @6
    @11
    cR
    wcel
    #
    @15
    @14
    @27
    @0
    @15
    @0
    @1
    @6
    @8
    @26
    simpl1l
    adantr
    @2
    @6
    @8
    @26
    @15
    simpll2
    @27
    @35
    @15
    @9
    @26
    @35
    @8
    @2
    @26
    @35
    wi
    #
    @6
    @8
    @24
    @36
    @25
    @24
    @26
    @35
    cV
    cR
    @10
    cA
    ffvelrn
    ex
    syl
    3ad2ant3
    imp
    adantr
    @27
    @15
    simpr
    cR
    cM
    @12
    cC
    @11
    @4
    rmsuppss.r
    @33
    @34
    domnmuln0
    syl112anc
    ex
    impbid
    rabeqbidva
    @9
    vw
    cV
    @13
    cvv
    @21
    cX
    cvv
    @4
    vv
    vw
    cV
    @20
    @13
    vv
    vw
    weq
    @19
    @11
    cC
    @12
    @18
    @10
    cA
    fveq2
    oveq2d
    cbvmptv
    @0
    @1
    @6
    @8
    simp1r
    @9
    cM
    c0g
    fvexd
    #
    @27
    cC
    @11
    @12
    ovexd
    mptsuppd
    @9
    cA
    wfun
    #
    @8
    @4
    cvv
    wcel
    @22
    @17
    wceq
    @8
    @2
    @38
    @6
    cA
    cR
    cV
    elmapfun
    3ad2ant3
    @2
    @6
    @8
    simp3
    @37
    vw
    @7
    cvv
    cA
    @4
    suppval1
    syl3anc
    3eqtr4d
end
