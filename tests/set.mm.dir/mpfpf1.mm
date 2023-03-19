include "wcel.mm"
include "ccrg.mm"
include "cv.mm"
include "c1o.mm"
include "cevl.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cpl1.mm"
include "cbs.mm"
include "wrex.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cvv.mm"
include "csubrg.mm"
include "crn.mm"
include "ces.mm"
include "eqid.mm"
include "evlval.mm"
include "rneqi.mm"
include "eqtri.mm"
include "mpfrcl.mm"
include "simp2d.mm"
include "id.mm"
include "syl6eleq.mm"
include "cmpl.mm"
include "cmap.mm"
include "cpws.mm"
include "crh.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "con0.mm"
include "1on.mm"
include "evlrhm.mm"
include "sylancr.mm"
include "cps1.mm"
include "ply1bas.mm"
include "rhmf.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "4syl.mm"
include "mpbid.mm"
include "wa.mm"
include "ce1.mm"
include "evl1val.mm"
include "evl1rhm.mm"
include "3syl.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "syl6eleqr.mm"
include "eqeltrrd.mm"
include "coeq1.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "sylc.mm"

theorem mpfpf1
  let vy: setvar y
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cE: class E
  let cF: class F
  let vx: setvar x
  let vz: setvar z
  assume pf1rcl.q: |- Q = ran ( eval1 ` R )
  assume pf1f.b: |- B = ( Base ` R )
  assume mpfpf1.q: |- E = ran ( 1o eval R )

  disjoint B y
  disjoint E y
  disjoint F y
  disjoint R y
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B z
  disjoint F x
  disjoint Q x
  disjoint R x
  assert |- ( F e. E -> ( F o. ( y e. B |-> ( 1o X. { y } ) ) ) e. Q )

  proof
    cF
    cE
    wcel
    #
    cR
    ccrg
    wcel
    #
    vx
    cv
    #
    c1o
    cR
    cevl
    co
    #
    cfv
    #
    cF
    wceq
    #
    vx
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
    vy
    cB
    c1o
    vy
    cv
    csn
    cxp
    cmpt
    #
    ccom
    #
    cQ
    wcel
    #
    @0
    c1o
    cvv
    wcel
    @1
    cB
    cR
    csubrg
    cfv
    wcel
    cE
    cB
    cR
    c1o
    cF
    cE
    @3
    crn
    #
    cB
    c1o
    cR
    ces
    co
    cfv
    #
    crn
    mpfpf1.q
    @3
    @13
    cB
    @3
    cR
    c1o
    @3
    eqid
    #
    pf1f.b
    evlval
    rneqi
    eqtri
    mpfrcl
    simp2d
    #
    @0
    cF
    @12
    wcel
    #
    @8
    @0
    cF
    cE
    @12
    @0
    id
    mpfpf1.q
    syl6eleq
    @0
    @3
    c1o
    cR
    cmpl
    co
    #
    cR
    cB
    c1o
    cmap
    co
    cpws
    co
    #
    crh
    co
    wcel
    #
    @7
    @18
    cbs
    cfv
    #
    @3
    wf
    @3
    @7
    wfn
    @16
    @8
    wb
    @0
    c1o
    con0
    wcel
    @1
    @19
    1on
    @15
    cB
    @3
    cR
    @18
    c1o
    con0
    @17
    @14
    pf1f.b
    @17
    eqid
    #
    @18
    eqid
    evlrhm
    sylancr
    @7
    @20
    @17
    @18
    @3
    @6
    cR
    cR
    cps1
    cfv
    #
    @7
    @6
    eqid
    #
    @22
    eqid
    @7
    eqid
    #
    ply1bas
    #
    @20
    eqid
    rhmf
    @7
    @20
    @3
    ffn
    vx
    @7
    cF
    @3
    fvelrnb
    4syl
    mpbid
    @1
    @5
    @11
    vx
    @7
    @1
    @2
    @7
    wcel
    #
    wa
    #
    @4
    @9
    ccom
    #
    cQ
    wcel
    @5
    @11
    @27
    @2
    cR
    ce1
    cfv
    #
    cfv
    #
    @28
    cQ
    vy
    @2
    cB
    @3
    cR
    @7
    @17
    @29
    @29
    eqid
    #
    @14
    pf1f.b
    @21
    @25
    evl1val
    @27
    @30
    @29
    crn
    #
    cQ
    @1
    @29
    @7
    wfn
    #
    @26
    @30
    @32
    wcel
    @1
    @29
    @6
    cR
    cB
    cpws
    co
    #
    crh
    co
    wcel
    @7
    @34
    cbs
    cfv
    #
    @29
    wf
    @33
    cB
    @6
    cR
    @34
    @29
    @31
    @23
    @34
    eqid
    pf1f.b
    evl1rhm
    @7
    @35
    @6
    @34
    @29
    @24
    @35
    eqid
    rhmf
    @7
    @35
    @29
    ffn
    3syl
    @7
    @2
    @29
    fnfvelrn
    sylan
    pf1rcl.q
    syl6eleqr
    eqeltrrd
    @5
    @28
    @10
    cQ
    @4
    cF
    @9
    coeq1
    eleq1d
    syl5ibcom
    rexlimdva
    sylc
end
