include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cexp.mm"
include "wa.mm"
include "cword.mm"
include "wrex.mm"
include "cio.mm"
include "id.mm"
include "cdm.mm"
include "cid.mm"
include "cdif.mm"
include "cfn.mm"
include "cop.mm"
include "c2.mm"
include "cpr.mm"
include "wo.mm"
include "elpri.mm"
include "prfi.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "diffi.mm"
include "syl.mm"
include "dmfi.mm"
include "3syl.mm"
include "cvv.mm"
include "cn.mm"
include "1ex.mm"
include "2nn.mm"
include "symg2bas.mm"
include "mp2an.mm"
include "eleq2s.mm"
include "psgneldm.mm"
include "sylanbrc.mm"
include "psgnval.mm"

theorem psgnprfval
  let vw: setvar w
  let cB: class B
  let cD: class D
  let cT: class T
  let cG: class G
  let cN: class N
  let cX: class X
  let vs: setvar s
  assume psgnprfval.0: |- D = { 1 , 2 }
  assume psgnprfval.g: |- G = ( SymGrp ` D )
  assume psgnprfval.b: |- B = ( Base ` G )
  assume psgnprfval.t: |- T = ran ( pmTrsp ` D )
  assume psgnprfval.n: |- N = ( pmSgn ` D )

  disjoint D s
  disjoint D w
  disjoint s w
  disjoint G s
  disjoint G w
  disjoint N s
  disjoint N w
  disjoint T s
  disjoint T w
  disjoint X s
  disjoint X w
  assert |- ( X e. B -> ( N ` X ) = ( iota s E. w e. Word T ( X = ( G gsum w ) /\ s = ( -u 1 ^ ( # ` w ) ) ) ) )

  proof
    cX
    cB
    wcel
    #
    @0
    cX
    cN
    cfv
    cX
    cG
    vw
    cv
    #
    cgsu
    co
    wceq
    vs
    cv
    c1
    cneg
    @1
    chash
    cfv
    cexp
    co
    wceq
    wa
    vw
    cT
    cword
    wrex
    vs
    cio
    wceq
    #
    @0
    id
    #
    @0
    cX
    cN
    cdm
    wcel
    #
    @2
    @0
    @0
    cX
    cid
    cdif
    #
    cdm
    cfn
    wcel
    #
    @4
    @3
    @6
    cX
    c1
    c1
    cop
    #
    c2
    c2
    cop
    #
    cpr
    #
    c1
    c2
    cop
    #
    c2
    c1
    cop
    #
    cpr
    #
    cpr
    #
    cB
    cX
    @13
    wcel
    cX
    @9
    wceq
    #
    cX
    @12
    wceq
    #
    wo
    #
    @5
    cfn
    wcel
    #
    @6
    cX
    @9
    @12
    elpri
    @16
    cX
    cfn
    wcel
    #
    @17
    @14
    @18
    @15
    @14
    @18
    @9
    cfn
    wcel
    @7
    @8
    prfi
    cX
    @9
    cfn
    eleq1
    mpbiri
    @15
    @18
    @12
    cfn
    wcel
    @10
    @11
    prfi
    cX
    @12
    cfn
    eleq1
    mpbiri
    jaoi
    cX
    cid
    diffi
    syl
    @5
    dmfi
    3syl
    c1
    cvv
    wcel
    c2
    cn
    wcel
    cB
    @13
    wceq
    1ex
    2nn
    cD
    cB
    cG
    c1
    c2
    cvv
    cn
    psgnprfval.g
    psgnprfval.b
    psgnprfval.0
    symg2bas
    mp2an
    eleq2s
    cB
    cD
    cX
    cG
    cN
    psgnprfval.g
    psgnprfval.n
    psgnprfval.b
    psgneldm
    sylanbrc
    vw
    cD
    cX
    cT
    cG
    cN
    vs
    psgnprfval.g
    psgnprfval.t
    psgnprfval.n
    psgnval
    syl
    syl
end
