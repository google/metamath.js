include "wcel.mm"
include "ccrg.mm"
include "cv.mm"
include "ce1.mm"
include "cfv.mm"
include "wceq.mm"
include "cpl1.mm"
include "cbs.mm"
include "wrex.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "cmpt.mm"
include "ccom.mm"
include "pf1rcl.mm"
include "crn.mm"
include "id.mm"
include "syl6eleq.mm"
include "cpws.mm"
include "crh.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "eqid.mm"
include "evl1rhm.mm"
include "syl.mm"
include "rhmf.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "4syl.mm"
include "mpbid.mm"
include "wa.mm"
include "cevl.mm"
include "csn.mm"
include "cxp.mm"
include "cid.mm"
include "cres.mm"
include "cmpl.mm"
include "cps1.mm"
include "ply1bas.mm"
include "evl1val.mm"
include "coeq1d.mm"
include "coass.mm"
include "ccnv.mm"
include "df1o2.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "0ex.mm"
include "mapsncnv.mm"
include "coeq1i.mm"
include "wf1o.mm"
include "mapsnf1o2.mm"
include "f1ococnv1.mm"
include "mp1i.mm"
include "syl5eqr.mm"
include "coeq2d.mm"
include "syl5eq.mm"
include "simpl.mm"
include "ovexd.mm"
include "con0.mm"
include "1on.mm"
include "evlrhm.mm"
include "mpan.mm"
include "ffvelrnda.mm"
include "pwselbas.mm"
include "fcoi1.mm"
include "3eqtrd.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "syl6eleqr.mm"
include "eqeltrd.mm"
include "coeq1.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "sylc.mm"

theorem pf1mpf
  let vx: setvar x
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cE: class E
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  assume pf1rcl.q: |- Q = ran ( eval1 ` R )
  assume pf1f.b: |- B = ( Base ` R )
  assume mpfpf1.q: |- E = ran ( 1o eval R )

  disjoint B x
  disjoint F x
  disjoint Q x
  disjoint R x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint E y
  disjoint F y
  disjoint R y
  assert |- ( F e. Q -> ( F o. ( x e. ( B ^m 1o ) |-> ( x ` (/) ) ) ) e. E )

  proof
    cF
    cQ
    wcel
    #
    cR
    ccrg
    wcel
    #
    vy
    cv
    #
    cR
    ce1
    cfv
    #
    cfv
    #
    cF
    wceq
    #
    vy
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    cF
    vx
    cB
    c1o
    cmap
    co
    #
    c0
    vx
    cv
    cfv
    cmpt
    #
    ccom
    #
    cE
    wcel
    #
    cQ
    cR
    cF
    pf1rcl.q
    pf1rcl
    #
    @0
    cF
    @3
    crn
    #
    wcel
    #
    @8
    @0
    cF
    cQ
    @14
    @0
    id
    pf1rcl.q
    syl6eleq
    @0
    @3
    @6
    cR
    cB
    cpws
    co
    #
    crh
    co
    wcel
    #
    @7
    @16
    cbs
    cfv
    #
    @3
    wf
    @3
    @7
    wfn
    @15
    @8
    wb
    @0
    @1
    @17
    @13
    cB
    @6
    cR
    @16
    @3
    @3
    eqid
    #
    @6
    eqid
    #
    @16
    eqid
    pf1f.b
    evl1rhm
    syl
    @7
    @18
    @6
    @16
    @3
    @7
    eqid
    #
    @18
    eqid
    rhmf
    @7
    @18
    @3
    ffn
    vy
    @7
    cF
    @3
    fvelrnb
    4syl
    mpbid
    @1
    @5
    @12
    vy
    @7
    @1
    @2
    @7
    wcel
    #
    wa
    #
    @4
    @10
    ccom
    #
    cE
    wcel
    @5
    @12
    @23
    @24
    @2
    c1o
    cR
    cevl
    co
    #
    cfv
    #
    cE
    @23
    @24
    @26
    vz
    cB
    c1o
    vz
    cv
    csn
    cxp
    cmpt
    #
    ccom
    #
    @10
    ccom
    #
    @26
    cid
    @9
    cres
    #
    ccom
    #
    @26
    @23
    @4
    @28
    @10
    vz
    @2
    cB
    @25
    cR
    @7
    c1o
    cR
    cmpl
    co
    #
    @3
    @19
    @25
    eqid
    #
    pf1f.b
    @32
    eqid
    #
    @6
    cR
    cR
    cps1
    cfv
    #
    @7
    @20
    @35
    eqid
    @21
    ply1bas
    #
    evl1val
    coeq1d
    @23
    @29
    @26
    @27
    @10
    ccom
    #
    ccom
    @31
    @26
    @27
    @10
    coass
    @23
    @37
    @30
    @26
    @23
    @37
    @10
    ccnv
    #
    @10
    ccom
    #
    @30
    @38
    @27
    @10
    vx
    vz
    cB
    c1o
    @10
    c0
    df1o2
    cB
    cR
    cbs
    cfv
    cvv
    pf1f.b
    cR
    cbs
    fvex
    eqeltri
    #
    0ex
    @10
    eqid
    #
    mapsncnv
    coeq1i
    @9
    cB
    @10
    wf1o
    @39
    @30
    wceq
    @23
    vx
    cB
    c1o
    @10
    c0
    df1o2
    @40
    0ex
    @41
    mapsnf1o2
    @9
    cB
    @10
    f1ococnv1
    mp1i
    syl5eqr
    coeq2d
    syl5eq
    @23
    @9
    cB
    @26
    wf
    @31
    @26
    wceq
    @23
    cB
    cR
    @9
    cR
    @9
    cpws
    co
    #
    cbs
    cfv
    #
    ccrg
    @26
    @42
    cvv
    @42
    eqid
    #
    pf1f.b
    @43
    eqid
    #
    @1
    @22
    simpl
    @23
    cB
    c1o
    cmap
    ovexd
    @1
    @7
    @43
    @2
    @25
    @1
    @25
    @32
    @42
    crh
    co
    wcel
    #
    @7
    @43
    @25
    wf
    #
    c1o
    con0
    wcel
    @1
    @46
    1on
    cB
    @25
    cR
    @42
    c1o
    con0
    @32
    @33
    pf1f.b
    @34
    @44
    evlrhm
    mpan
    @7
    @43
    @32
    @42
    @25
    @36
    @45
    rhmf
    syl
    #
    ffvelrnda
    pwselbas
    @9
    cB
    @26
    fcoi1
    syl
    3eqtrd
    @23
    @26
    @25
    crn
    #
    cE
    @1
    @25
    @7
    wfn
    #
    @22
    @26
    @49
    wcel
    @1
    @47
    @50
    @48
    @7
    @43
    @25
    ffn
    syl
    @7
    @2
    @25
    fnfvelrn
    sylan
    mpfpf1.q
    syl6eleqr
    eqeltrd
    @5
    @24
    @11
    cE
    @4
    cF
    @10
    coeq1
    eleq1d
    syl5ibcom
    rexlimdva
    sylc
end
