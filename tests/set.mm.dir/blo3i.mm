include "wcel.mm"
include "cr.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "isblo3i.mm"
include "biimpri.mm"
include "sylan2.mm"
include "3impb.mm"

theorem blo3i
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cT: class T
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume isblo3i.1: |- X = ( BaseSet ` U )
  assume isblo3i.m: |- M = ( normCV ` U )
  assume isblo3i.n: |- N = ( normCV ` W )
  assume isblo3i.4: |- L = ( U LnOp W )
  assume isblo3i.5: |- B = ( U BLnOp W )
  assume isblo3i.u: |- U e. NrmCVec
  assume isblo3i.w: |- W e. NrmCVec

  disjoint A y
  disjoint B y
  disjoint M y
  disjoint N y
  disjoint T y
  disjoint U y
  disjoint W y
  disjoint X y
  disjoint x y
  disjoint A x
  disjoint B x
  disjoint L x
  disjoint M x
  disjoint N x
  disjoint T x
  disjoint U x
  disjoint W x
  disjoint X x
  assert |- ( ( T e. L /\ A e. RR /\ A. y e. X ( N ` ( T ` y ) ) <_ ( A x. ( M ` y ) ) ) -> T e. B )

  proof
    cT
    cL
    wcel
    #
    cA
    cr
    wcel
    #
    vy
    cv
    #
    cT
    cfv
    cN
    cfv
    #
    cA
    @2
    cM
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    cT
    cB
    wcel
    #
    @1
    @7
    wa
    @0
    @3
    vx
    cv
    #
    @4
    cmul
    co
    #
    cle
    wbr
    #
    vy
    cX
    wral
    #
    vx
    cr
    wrex
    #
    @8
    @12
    @7
    vx
    cA
    cr
    @9
    cA
    wceq
    #
    @11
    @6
    vy
    cX
    @14
    @10
    @5
    @3
    cle
    @9
    cA
    @4
    cmul
    oveq1
    breq2d
    ralbidv
    rspcev
    @8
    @0
    @13
    wa
    vx
    vy
    cB
    cT
    cU
    cL
    cM
    cN
    cW
    cX
    isblo3i.1
    isblo3i.m
    isblo3i.n
    isblo3i.4
    isblo3i.5
    isblo3i.u
    isblo3i.w
    isblo3i
    biimpri
    sylan2
    3impb
end
