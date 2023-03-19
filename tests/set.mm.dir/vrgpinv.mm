include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c0.mm"
include "cop.mm"
include "cs1.mm"
include "cec.mm"
include "c2o.mm"
include "cv.mm"
include "c1o.mm"
include "cdif.mm"
include "cmpt2.mm"
include "creverse.mm"
include "ccom.mm"
include "vrgpval.mm"
include "fveq2d.mm"
include "cxp.mm"
include "cword.mm"
include "cid.mm"
include "wceq.mm"
include "simpr.mm"
include "cpr.mm"
include "0ex.mm"
include "prid1.mm"
include "df2o3.mm"
include "eleqtrri.mm"
include "opelxpi.mm"
include "sylancl.mm"
include "s1cld.mm"
include "cvv.mm"
include "con0.mm"
include "simpl.mm"
include "2on.mm"
include "xpexg.mm"
include "wrdexg.mm"
include "fvi.mm"
include "3syl.mm"
include "eleqtrrd.mm"
include "eqid.mm"
include "frgpinv.mm"
include "syl.mm"
include "revs1.mm"
include "a1i.mm"
include "coeq2d.mm"
include "wf.mm"
include "efgmf.mm"
include "s1co.mm"
include "co.mm"
include "efgmval.mm"
include "df-ov.mm"
include "dif0.mm"
include "opeq2i.mm"
include "3eqtr3g.mm"
include "s1eqd.mm"
include "3eqtrd.mm"
include "eceq1d.mm"

theorem vrgpinv
  let cA: class A
  let c.sm: class .~
  let cU: class U
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let vj: setvar j
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  assume vrgpfval.r: |- .~ = ( ~FG ` I )
  assume vrgpfval.u: |- U = ( varFGrp ` I )
  assume vrgpf.m: |- G = ( freeGrp ` I )
  assume vrgpinv.n: |- N = ( invg ` G )


  assert |- ( ( I e. V /\ A e. I ) -> ( N ` ( U ` A ) ) = [ <" <. A , 1o >. "> ] .~ )

  proof
    cI
    cV
    wcel
    #
    cA
    cI
    wcel
    #
    wa
    #
    cA
    cU
    cfv
    #
    cN
    cfv
    cA
    c0
    cop
    #
    cs1
    #
    c.sm
    cec
    #
    cN
    cfv
    #
    vx
    vy
    cI
    c2o
    vx
    cv
    c1o
    vy
    cv
    cdif
    cop
    cmpt2
    #
    @5
    creverse
    cfv
    #
    ccom
    #
    c.sm
    cec
    #
    cA
    c1o
    cop
    #
    cs1
    #
    c.sm
    cec
    @2
    @3
    @6
    cN
    cA
    c.sm
    cU
    cI
    cV
    vrgpfval.r
    vrgpfval.u
    vrgpval
    fveq2d
    @2
    @5
    cI
    c2o
    cxp
    #
    cword
    #
    cid
    cfv
    #
    wcel
    @7
    @11
    wceq
    @2
    @5
    @15
    @16
    @2
    @4
    @14
    @2
    @1
    c0
    c2o
    wcel
    #
    @4
    @14
    wcel
    #
    @0
    @1
    simpr
    #
    c0
    c0
    c1o
    cpr
    c2o
    c0
    c1o
    0ex
    prid1
    df2o3
    eleqtrri
    #
    cA
    c0
    cI
    c2o
    opelxpi
    sylancl
    #
    s1cld
    @2
    @14
    cvv
    wcel
    #
    @15
    cvv
    wcel
    @16
    @15
    wceq
    @2
    @0
    c2o
    con0
    wcel
    @22
    @0
    @1
    simpl
    2on
    cI
    c2o
    cV
    con0
    xpexg
    sylancl
    @14
    cvv
    wrdexg
    @15
    cvv
    fvi
    3syl
    eleqtrrd
    vx
    vy
    @5
    c.sm
    cG
    cI
    @8
    cN
    @16
    @16
    eqid
    vrgpf.m
    vrgpfval.r
    vrgpinv.n
    @8
    eqid
    #
    frgpinv
    syl
    @2
    @10
    @13
    c.sm
    @2
    @10
    @8
    @5
    ccom
    #
    @4
    @8
    cfv
    #
    cs1
    #
    @13
    @2
    @9
    @5
    @8
    @9
    @5
    wceq
    @2
    @4
    revs1
    a1i
    coeq2d
    @2
    @18
    @14
    @14
    @8
    wf
    @24
    @26
    wceq
    @21
    vx
    vy
    cI
    @8
    @23
    efgmf
    @14
    @14
    @4
    @8
    s1co
    sylancl
    @2
    @25
    @12
    @2
    cA
    c0
    @8
    co
    #
    cA
    c1o
    c0
    cdif
    #
    cop
    #
    @25
    @12
    @2
    @1
    @17
    @27
    @29
    wceq
    @19
    @20
    vx
    vy
    cA
    c0
    cI
    @8
    @23
    efgmval
    sylancl
    cA
    c0
    @8
    df-ov
    @28
    c1o
    cA
    c1o
    dif0
    opeq2i
    3eqtr3g
    s1eqd
    3eqtrd
    eceq1d
    3eqtrd
end
