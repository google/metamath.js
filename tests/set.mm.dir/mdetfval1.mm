include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "ccom.mm"
include "mdetfval.mm"
include "wa.mm"
include "zrhcofipsgn.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "wn.mm"
include "wnel.mm"
include "df-nel.mm"
include "c0.mm"
include "nfimdetndef.mm"
include "cmat.mm"
include "cbs.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "cvv.mm"
include "biimpi.mm"
include "intnanrd.mm"
include "matbas0.mm"
include "syl.mm"
include "mpteq1d.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "sylbir.mm"
include "pm2.61i.mm"

theorem mdetfval1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vm: setvar m
  let cN: class N
  let cY: class Y
  let vp: setvar p
  assume mdetfval1.d: |- D = ( N maDet R )
  assume mdetfval1.a: |- A = ( N Mat R )
  assume mdetfval1.b: |- B = ( Base ` A )
  assume mdetfval1.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume mdetfval1.y: |- Y = ( ZRHom ` R )
  assume mdetfval1.s: |- S = ( pmSgn ` N )
  assume mdetfval1.t: |- .x. = ( .r ` R )
  assume mdetfval1.u: |- U = ( mulGrp ` R )

  disjoint m p
  disjoint B m
  disjoint B p
  disjoint m x
  disjoint N m
  disjoint p x
  disjoint N p
  disjoint N x
  disjoint P m
  disjoint P p
  disjoint R m
  disjoint R p
  disjoint R x
  disjoint S m
  disjoint U m
  disjoint Y m
  disjoint .x. m
  assert |- D = ( m e. B |-> ( R gsum ( p e. P |-> ( ( Y ` ( S ` p ) ) .x. ( U gsum ( x e. N |-> ( ( p ` x ) m x ) ) ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cD
    vm
    cB
    cR
    vp
    cP
    vp
    cv
    #
    cS
    cfv
    cY
    cfv
    #
    cU
    vx
    cN
    vx
    cv
    #
    @1
    cfv
    @3
    vm
    cv
    co
    cmpt
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    wceq
    #
    @0
    cD
    vm
    cB
    cR
    vp
    cP
    @1
    cY
    cS
    ccom
    cfv
    #
    @4
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    @8
    vx
    cA
    cB
    cD
    cP
    cR
    cS
    c.x
    cU
    vm
    cN
    cY
    vp
    mdetfval1.d
    mdetfval1.a
    mdetfval1.b
    mdetfval1.p
    mdetfval1.y
    mdetfval1.s
    mdetfval1.t
    mdetfval1.u
    mdetfval
    @0
    vm
    cB
    @13
    @7
    @0
    @12
    @6
    cR
    cgsu
    @0
    vp
    cP
    @11
    @5
    @0
    @1
    cP
    wcel
    wa
    @10
    @2
    @4
    c.x
    cP
    @1
    cR
    cS
    cN
    cY
    mdetfval1.p
    mdetfval1.y
    mdetfval1.s
    zrhcofipsgn
    oveq1d
    mpteq2dva
    oveq2d
    mpteq2dv
    syl5eq
    @0
    wn
    #
    cN
    cfn
    wnel
    #
    @9
    cN
    cfn
    df-nel
    #
    @15
    cD
    c0
    @8
    cD
    cR
    cN
    mdetfval1.d
    nfimdetndef
    @15
    @8
    vm
    c0
    @7
    cmpt
    c0
    @15
    vm
    cB
    c0
    @7
    @15
    cB
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    c0
    cB
    cA
    cbs
    cfv
    @18
    mdetfval1.b
    cA
    @17
    cbs
    mdetfval1.a
    fveq2i
    eqtri
    @15
    @0
    cR
    cvv
    wcel
    #
    wa
    wn
    @18
    c0
    wceq
    @15
    @0
    @19
    @15
    @14
    @16
    biimpi
    intnanrd
    cR
    cN
    matbas0
    syl
    syl5eq
    mpteq1d
    vm
    @7
    mpt0
    syl6eq
    eqtr4d
    sylbir
    pm2.61i
end
