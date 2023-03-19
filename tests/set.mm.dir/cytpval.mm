include "ccnfld.mm"
include "cpl1.mm"
include "cfv.mm"
include "cmgp.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cress.mm"
include "co.mm"
include "cod.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cv1.mm"
include "cascl.mm"
include "csg.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cn.mm"
include "ccytp.mm"
include "wceq.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "eqtri.mm"
include "cnveqi.mm"
include "imaeq1i.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "syl5eqr.mm"
include "fveq1i.mm"
include "oveq123i.mm"
include "mpteq12dv.mm"
include "oveq12d.mm"
include "df-cytp.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem cytpval
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let c.mi: class .-
  let cN: class N
  let cO: class O
  let cX: class X
  let vr: setvar r
  let vn: setvar n
  assume cytpval.t: |- T = ( ( mulGrp ` CCfld ) |`s ( CC \ { 0 } ) )
  assume cytpval.o: |- O = ( od ` T )
  assume cytpval.p: |- P = ( Poly1 ` CCfld )
  assume cytpval.x: |- X = ( var1 ` CCfld )
  assume cytpval.q: |- Q = ( mulGrp ` P )
  assume cytpval.m: |- .- = ( -g ` P )
  assume cytpval.a: |- A = ( algSc ` P )

  disjoint N r
  disjoint n r
  disjoint N n
  disjoint A n
  disjoint .- n
  disjoint O n
  disjoint Q n
  disjoint X n
  assert |- ( N e. NN -> ( CytP ` N ) = ( Q gsum ( r e. ( `' O " { N } ) |-> ( X .- ( A ` r ) ) ) ) )

  proof
    vn
    cN
    ccnfld
    cpl1
    cfv
    #
    cmgp
    cfv
    #
    vr
    ccnfld
    cmgp
    cfv
    cc
    cc0
    csn
    cdif
    cress
    co
    #
    cod
    cfv
    #
    ccnv
    #
    vn
    cv
    #
    csn
    #
    cima
    #
    ccnfld
    cv1
    cfv
    #
    vr
    cv
    #
    @0
    cascl
    cfv
    #
    cfv
    #
    @0
    csg
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    cQ
    vr
    cO
    ccnv
    #
    cN
    csn
    #
    cima
    #
    cX
    @9
    cA
    cfv
    #
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    cn
    ccytp
    @5
    cN
    wceq
    #
    @1
    cQ
    @14
    @20
    cgsu
    @1
    cQ
    wceq
    @21
    @1
    cP
    cmgp
    cfv
    cQ
    @0
    cP
    cmgp
    cP
    @0
    cytpval.p
    eqcomi
    fveq2i
    cytpval.q
    eqtr4i
    a1i
    @21
    vr
    @7
    @13
    @17
    @19
    @21
    @7
    @15
    @6
    cima
    @17
    @15
    @4
    @6
    cO
    @3
    cO
    cT
    cod
    cfv
    @3
    cytpval.o
    cT
    @2
    cod
    cytpval.t
    fveq2i
    eqtri
    cnveqi
    imaeq1i
    @21
    @6
    @16
    @15
    @5
    cN
    sneq
    imaeq2d
    syl5eqr
    @13
    @19
    wceq
    @21
    @19
    @13
    cX
    @18
    @8
    @11
    c.mi
    @12
    cytpval.x
    @9
    cA
    @10
    cA
    cP
    cascl
    cfv
    @10
    cytpval.a
    cP
    @0
    cascl
    cytpval.p
    fveq2i
    eqtri
    fveq1i
    c.mi
    cP
    csg
    cfv
    @12
    cytpval.m
    cP
    @0
    csg
    cytpval.p
    fveq2i
    eqtri
    oveq123i
    eqcomi
    a1i
    mpteq12dv
    oveq12d
    vn
    vr
    df-cytp
    cQ
    @20
    cgsu
    ovex
    fvmpt
end
