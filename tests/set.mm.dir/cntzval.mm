include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "cpw.mm"
include "cmpt.mm"
include "cntzfval.mm"
include "fveq1d.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "raleq.mm"
include "rabbidv.mm"
include "eqid.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylbir.mm"
include "sylan9eq.mm"
include "wn.mm"
include "c0.mm"
include "0fv.mm"
include "ccntz.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "ssrab2.mm"
include "syl5sseq.mm"
include "ss0.mm"
include "syl.mm"
include "3eqtr4a.mm"
include "adantr.mm"
include "pm2.61ian.mm"

theorem cntzval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vs: setvar s
  let cA: class A
  let cT: class T
  let cX: class X
  let cY: class Y
  assume cntzfval.b: |- B = ( Base ` M )
  assume cntzfval.p: |- .+ = ( +g ` M )
  assume cntzfval.z: |- Z = ( Cntz ` M )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint B x
  disjoint M x
  disjoint M y
  disjoint S x
  disjoint S y
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint .+ m
  disjoint s x
  disjoint s y
  disjoint .+ s
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint B s
  disjoint M m
  disjoint M s
  disjoint T x
  disjoint T y
  disjoint S s
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( S C_ B -> ( Z ` S ) = { x e. B | A. y e. S ( x .+ y ) = ( y .+ x ) } )

  proof
    cM
    cvv
    wcel
    #
    cS
    cB
    wss
    #
    cS
    cZ
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    @4
    @3
    c.pl
    co
    wceq
    #
    vy
    cS
    wral
    #
    vx
    cB
    crab
    #
    wceq
    #
    @0
    @1
    @2
    cS
    vs
    cB
    cpw
    #
    @5
    vy
    vs
    cv
    #
    wral
    #
    vx
    cB
    crab
    #
    cmpt
    #
    cfv
    #
    @7
    @0
    cS
    cZ
    @13
    vx
    vy
    cB
    c.pl
    cM
    cvv
    cZ
    vs
    cntzfval.b
    cntzfval.p
    cntzfval.z
    cntzfval
    fveq1d
    @1
    cS
    @9
    wcel
    @14
    @7
    wceq
    cS
    cB
    cB
    cM
    cbs
    cfv
    #
    cvv
    cntzfval.b
    cM
    cbs
    fvex
    eqeltri
    #
    elpw2
    vs
    cS
    @12
    @7
    @9
    @13
    @10
    cS
    wceq
    @11
    @6
    vx
    cB
    @5
    vy
    @10
    cS
    raleq
    rabbidv
    @13
    eqid
    @6
    vx
    cB
    @16
    rabex
    fvmpt
    sylbir
    sylan9eq
    @0
    wn
    #
    @8
    @1
    @17
    cS
    c0
    cfv
    c0
    @2
    @7
    cS
    0fv
    @17
    cS
    cZ
    c0
    @17
    cZ
    cM
    ccntz
    cfv
    c0
    cntzfval.z
    cM
    ccntz
    fvprc
    syl5eq
    fveq1d
    @17
    @7
    c0
    wss
    @7
    c0
    wceq
    @17
    cB
    @7
    c0
    @6
    vx
    cB
    ssrab2
    @17
    cB
    @15
    c0
    cntzfval.b
    cM
    cbs
    fvprc
    syl5eq
    syl5sseq
    @7
    ss0
    syl
    3eqtr4a
    adantr
    pm2.61ian
end
