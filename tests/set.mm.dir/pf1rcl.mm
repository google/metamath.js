include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "ccrg.mm"
include "n0i.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cevl.mm"
include "crn.mm"
include "cima.mm"
include "ce1.mm"
include "eqid.mm"
include "evl1fval.mm"
include "rneqi.mm"
include "rnco2.mm"
include "3eqtri.mm"
include "cdm.mm"
include "cin.mm"
include "wss.mm"
include "inss2.mm"
include "wex.mm"
include "neq0.mm"
include "cvv.mm"
include "csubrg.mm"
include "ces.mm"
include "evlval.mm"
include "mpfrcl.mm"
include "simp2d.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "con1i.mm"
include "sseq0.mm"
include "sylancr.mm"
include "imadisj.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "nsyl2.mm"

theorem pf1rcl
  let cQ: class Q
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cE: class E
  let cF: class F
  assume pf1rcl.q: |- Q = ran ( eval1 ` R )


  assert |- ( X e. Q -> R e. CRing )

  proof
    cX
    cQ
    wcel
    cQ
    c0
    wceq
    cR
    ccrg
    wcel
    #
    cQ
    cX
    n0i
    @0
    wn
    #
    cQ
    vx
    cR
    cbs
    cfv
    #
    @2
    c1o
    cmap
    co
    cmap
    co
    vx
    cv
    #
    vy
    @2
    c1o
    vy
    cv
    csn
    cxp
    cmpt
    ccom
    cmpt
    #
    c1o
    cR
    cevl
    co
    #
    crn
    #
    cima
    #
    c0
    cQ
    cR
    ce1
    cfv
    #
    crn
    @4
    @5
    ccom
    #
    crn
    @7
    pf1rcl.q
    @8
    @9
    vx
    vy
    @2
    @5
    cR
    @8
    @8
    eqid
    @5
    eqid
    #
    @2
    eqid
    #
    evl1fval
    rneqi
    @4
    @5
    rnco2
    3eqtri
    @1
    @4
    cdm
    #
    @6
    cin
    #
    c0
    wceq
    #
    @7
    c0
    wceq
    @1
    @13
    @6
    wss
    @6
    c0
    wceq
    #
    @14
    @12
    @6
    inss2
    @15
    @0
    @15
    wn
    @3
    @6
    wcel
    #
    vx
    wex
    @0
    vx
    @6
    neq0
    @16
    @0
    vx
    @16
    c1o
    cvv
    wcel
    @0
    @2
    cR
    csubrg
    cfv
    wcel
    @6
    @2
    cR
    c1o
    @3
    @5
    @2
    c1o
    cR
    ces
    co
    cfv
    @2
    @5
    cR
    c1o
    @10
    @11
    evlval
    rneqi
    mpfrcl
    simp2d
    exlimiv
    sylbi
    con1i
    @13
    @6
    sseq0
    sylancr
    @4
    @6
    imadisj
    sylibr
    syl5eq
    nsyl2
end
