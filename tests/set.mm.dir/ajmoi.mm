include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wmo.mm"
include "wi.mm"
include "wal.mm"
include "r19.26-2.mm"
include "eqtr2.mm"
include "2ralimi.mm"
include "sylbir.mm"
include "phoeqi.mm"
include "biimpa.mm"
include "sylan2.mm"
include "an4s.mm"
include "gen2.mm"
include "feq1.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "mo4.mm"
include "mpbir.mm"

theorem ajmoi
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let cA: class A
  let cB: class B
  let vt: setvar t
  let cS: class S
  assume ip2eqi.1: |- X = ( BaseSet ` U )
  assume ip2eqi.7: |- P = ( .iOLD ` U )
  assume ip2eqi.u: |- U e. CPreHilOLD

  disjoint s x
  disjoint P s
  disjoint P x
  disjoint Q s
  disjoint x y
  disjoint s y
  disjoint T s
  disjoint T x
  disjoint T y
  disjoint U x
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint Y s
  disjoint Y x
  disjoint Y y
  disjoint A x
  disjoint B x
  disjoint s t
  disjoint t x
  disjoint P t
  disjoint Q t
  disjoint S x
  disjoint S y
  disjoint t y
  disjoint T t
  disjoint X t
  disjoint Y t
  assert |- E* s ( s : Y --> X /\ A. x e. X A. y e. Y ( ( T ` x ) Q y ) = ( x P ( s ` y ) ) )

  proof
    cY
    cX
    vs
    cv
    #
    wf
    #
    vx
    cv
    #
    cT
    cfv
    vy
    cv
    #
    cQ
    co
    #
    @2
    @3
    @0
    cfv
    #
    cP
    co
    #
    wceq
    #
    vy
    cY
    wral
    vx
    cX
    wral
    #
    wa
    #
    vs
    wmo
    @9
    cY
    cX
    vt
    cv
    #
    wf
    #
    @4
    @2
    @3
    @10
    cfv
    #
    cP
    co
    #
    wceq
    #
    vy
    cY
    wral
    vx
    cX
    wral
    #
    wa
    #
    wa
    @0
    @10
    wceq
    #
    wi
    #
    vt
    wal
    vs
    wal
    @18
    vs
    vt
    @1
    @11
    @8
    @15
    @17
    @8
    @15
    wa
    #
    @1
    @11
    wa
    #
    @6
    @13
    wceq
    #
    vy
    cY
    wral
    vx
    cX
    wral
    #
    @17
    @19
    @7
    @14
    wa
    #
    vy
    cY
    wral
    vx
    cX
    wral
    @22
    @7
    @14
    vx
    vy
    cX
    cY
    r19.26-2
    @23
    @21
    vx
    vy
    cX
    cY
    @4
    @6
    @13
    eqtr2
    2ralimi
    sylbir
    @20
    @22
    @17
    vx
    vy
    cP
    @0
    @10
    cU
    cX
    cY
    ip2eqi.1
    ip2eqi.7
    ip2eqi.u
    phoeqi
    biimpa
    sylan2
    an4s
    gen2
    @9
    @16
    vs
    vt
    @17
    @1
    @11
    @8
    @15
    cY
    cX
    @0
    @10
    feq1
    @17
    @7
    @14
    vx
    vy
    cX
    cY
    @17
    @6
    @13
    @4
    @17
    @5
    @12
    @2
    cP
    @3
    @0
    @10
    fveq1
    oveq2d
    eqeq2d
    2ralbidv
    anbi12d
    mo4
    mpbir
end
