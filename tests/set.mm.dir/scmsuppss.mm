include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "c0g.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "csupp.mm"
include "wss.mm"
include "wf.mm"
include "wi.mm"
include "elmapi.mm"
include "wceq.mm"
include "fdm.mm"
include "wa.mm"
include "cvv.mm"
include "eqidd.mm"
include "weq.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "adantl.mm"
include "simpr.mm"
include "ovex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "neeq1d.mm"
include "oveq1.mm"
include "simplrr.mm"
include "elelpwi.mm"
include "expcom.mm"
include "adantr.mm"
include "imp.mm"
include "eqid.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "necon3d.mm"
include "sylbid.mm"
include "ss2rabdv.mm"
include "wb.mm"
include "dmmpti.mm"
include "rabeq.mm"
include "mp1i.mm"
include "sseq12d.mm"
include "mpbird.mm"
include "exp43.mm"
include "mpcom.mm"
include "syl.mm"
include "com13.mm"
include "3imp.mm"
include "wfun.mm"
include "funmpt.mm"
include "mptexg.mm"
include "3ad2ant2.mm"
include "fvexd.mm"
include "suppval1.mm"
include "syl3anc.mm"
include "elmapfun.mm"
include "3ad2ant3.mm"
include "simp3.mm"
include "3sstr4d.mm"

theorem scmsuppss
  let vv: setvar v
  let cA: class A
  let cR: class R
  let cS: class S
  let cM: class M
  let cV: class V
  let vx: setvar x
  let vk: setvar k
  assume scmsuppss.s: |- S = ( Scalar ` M )
  assume scmsuppss.r: |- R = ( Base ` S )

  disjoint A v
  disjoint M v
  disjoint R v
  disjoint V v
  disjoint A x
  disjoint v x
  disjoint M x
  disjoint R x
  disjoint S x
  disjoint V x
  disjoint k x
  assert |- ( ( M e. LMod /\ V e. ~P ( Base ` M ) /\ A e. ( R ^m V ) ) -> ( ( v e. V |-> ( ( A ` v ) ( .s ` M ) v ) ) supp ( 0g ` M ) ) C_ ( A supp ( 0g ` S ) ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
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
    vx
    cv
    #
    vv
    cV
    vv
    cv
    #
    cA
    cfv
    #
    @8
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cfv
    #
    cM
    c0g
    cfv
    #
    wne
    #
    vx
    @12
    cdm
    #
    crab
    #
    @7
    cA
    cfv
    #
    cS
    c0g
    cfv
    #
    wne
    #
    vx
    cA
    cdm
    #
    crab
    #
    @12
    @14
    csupp
    co
    #
    cA
    @19
    csupp
    co
    #
    @0
    @3
    @5
    @17
    @22
    wss
    #
    @5
    @3
    @0
    @25
    @5
    cV
    cR
    cA
    wf
    #
    @3
    @0
    @25
    wi
    wi
    #
    cA
    cR
    cV
    elmapi
    @21
    cV
    wceq
    #
    @26
    @27
    cV
    cR
    cA
    fdm
    @28
    @26
    @3
    @0
    @25
    @28
    @26
    wa
    #
    @3
    @0
    wa
    #
    wa
    #
    @25
    @15
    vx
    cV
    crab
    #
    @20
    vx
    cV
    crab
    #
    wss
    #
    @31
    @15
    @20
    vx
    cV
    @31
    @7
    cV
    wcel
    #
    wa
    #
    @15
    @18
    @7
    @10
    co
    #
    @14
    wne
    @20
    @36
    @13
    @37
    @14
    @36
    vv
    @7
    @11
    @37
    cV
    @12
    cvv
    @36
    @12
    eqidd
    vv
    vx
    weq
    #
    @11
    @37
    wceq
    @36
    @38
    @9
    @18
    @8
    @7
    @10
    @8
    @7
    cA
    fveq2
    @38
    id
    oveq12d
    adantl
    @31
    @35
    simpr
    @37
    cvv
    wcel
    @36
    @18
    @7
    @10
    ovex
    a1i
    fvmptd
    neeq1d
    @36
    @18
    @19
    @37
    @14
    @36
    @18
    @19
    wceq
    #
    @37
    @14
    wceq
    @39
    @36
    @37
    @19
    @7
    @10
    co
    #
    @14
    @18
    @19
    @7
    @10
    oveq1
    @36
    @0
    @7
    @1
    wcel
    #
    @40
    @14
    wceq
    @29
    @3
    @0
    @35
    simplrr
    @31
    @35
    @41
    @30
    @35
    @41
    wi
    #
    @29
    @3
    @42
    @0
    @35
    @3
    @41
    @7
    cV
    @1
    elelpwi
    expcom
    adantr
    adantl
    imp
    @10
    cS
    @19
    @1
    cM
    @7
    @14
    @1
    eqid
    scmsuppss.s
    @10
    eqid
    @19
    eqid
    @14
    eqid
    lmod0vs
    syl2anc
    sylan9eqr
    ex
    necon3d
    sylbid
    ss2rabdv
    @29
    @25
    @34
    wb
    #
    @30
    @28
    @43
    @26
    @28
    @17
    @32
    @22
    @33
    @16
    cV
    wceq
    @17
    @32
    wceq
    @28
    vv
    cV
    @11
    @12
    @9
    @8
    @10
    ovex
    @12
    eqid
    dmmpti
    @15
    vx
    @16
    cV
    rabeq
    mp1i
    @20
    vx
    @21
    cV
    rabeq
    sseq12d
    adantr
    adantr
    mpbird
    exp43
    mpcom
    syl
    com13
    3imp
    @6
    @12
    wfun
    #
    @12
    cvv
    wcel
    #
    @14
    cvv
    wcel
    @23
    @17
    wceq
    @44
    @6
    vv
    cV
    @11
    funmpt
    a1i
    @3
    @0
    @45
    @5
    vv
    cV
    @11
    @2
    mptexg
    3ad2ant2
    @6
    cM
    c0g
    fvexd
    vx
    cvv
    cvv
    @12
    @14
    suppval1
    syl3anc
    @6
    cA
    wfun
    #
    @5
    @19
    cvv
    wcel
    @24
    @22
    wceq
    @5
    @0
    @46
    @3
    cA
    cR
    cV
    elmapfun
    3ad2ant3
    @0
    @3
    @5
    simp3
    @6
    cS
    c0g
    fvexd
    vx
    @4
    cvv
    cA
    @19
    suppval1
    syl3anc
    3sstr4d
end
