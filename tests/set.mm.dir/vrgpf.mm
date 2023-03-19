include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "c0.mm"
include "cop.mm"
include "cs1.mm"
include "cec.mm"
include "cmpt.mm"
include "wa.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "cid.mm"
include "cfv.mm"
include "c1o.mm"
include "cpr.mm"
include "0ex.mm"
include "prid1.mm"
include "df2o3.mm"
include "eleqtrri.mm"
include "opelxpi.mm"
include "mpan2.mm"
include "adantl.mm"
include "s1cld.mm"
include "cvv.mm"
include "wceq.mm"
include "con0.mm"
include "2on.mm"
include "xpexg.mm"
include "adantr.mm"
include "wrdexg.mm"
include "fvi.mm"
include "3syl.mm"
include "eleqtrrd.mm"
include "eqid.mm"
include "frgpeccl.mm"
include "syl.mm"
include "fmptd.mm"
include "vrgpfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem vrgpf
  let c.sm: class .~
  let cU: class U
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let cA: class A
  let vj: setvar j
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  assume vrgpfval.r: |- .~ = ( ~FG ` I )
  assume vrgpfval.u: |- U = ( varFGrp ` I )
  assume vrgpf.m: |- G = ( freeGrp ` I )
  assume vrgpf.x: |- X = ( Base ` G )


  assert |- ( I e. V -> U : I --> X )

  proof
    cI
    cV
    wcel
    #
    cI
    cX
    cU
    wf
    cI
    cX
    vj
    cI
    vj
    cv
    #
    c0
    cop
    #
    cs1
    #
    c.sm
    cec
    #
    cmpt
    #
    wf
    @0
    vj
    cI
    @4
    cX
    @5
    @0
    @1
    cI
    wcel
    #
    wa
    #
    @3
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
    @4
    cX
    wcel
    @7
    @3
    @9
    @10
    @7
    @2
    @8
    @6
    @2
    @8
    wcel
    #
    @0
    @6
    c0
    c2o
    wcel
    @11
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
    @1
    c0
    cI
    c2o
    opelxpi
    mpan2
    adantl
    s1cld
    @7
    @8
    cvv
    wcel
    #
    @9
    cvv
    wcel
    @10
    @9
    wceq
    @0
    @12
    @6
    @0
    c2o
    con0
    wcel
    @12
    2on
    cI
    c2o
    cV
    con0
    xpexg
    mpan2
    adantr
    @8
    cvv
    wrdexg
    @9
    cvv
    fvi
    3syl
    eleqtrrd
    cX
    c.sm
    cG
    cI
    @10
    @3
    vrgpf.m
    vrgpfval.r
    @10
    eqid
    vrgpf.x
    frgpeccl
    syl
    @5
    eqid
    fmptd
    @0
    cI
    cX
    cU
    @5
    c.sm
    cU
    vj
    cI
    cV
    vrgpfval.r
    vrgpfval.u
    vrgpfval
    feq1d
    mpbird
end
