include "wcel.mm"
include "ccntz.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "cmpt.mm"
include "cvv.mm"
include "elex.mm"
include "cbs.mm"
include "cplusg.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "df-cntz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem cntzfval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vs: setvar s
  let vm: setvar m
  let cA: class A
  let cT: class T
  let cS: class S
  let cX: class X
  let cY: class Y
  assume cntzfval.b: |- B = ( Base ` M )
  assume cntzfval.p: |- .+ = ( +g ` M )
  assume cntzfval.z: |- Z = ( Cntz ` M )

  disjoint s x
  disjoint s y
  disjoint .+ s
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint B s
  disjoint B x
  disjoint M s
  disjoint M x
  disjoint M y
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint .+ m
  disjoint A x
  disjoint A y
  disjoint B m
  disjoint M m
  disjoint T x
  disjoint T y
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( M e. V -> Z = ( s e. ~P B |-> { x e. B | A. y e. s ( x .+ y ) = ( y .+ x ) } ) )

  proof
    cM
    cV
    wcel
    #
    cZ
    cM
    ccntz
    cfv
    #
    vs
    cB
    cpw
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    @4
    @3
    c.pl
    co
    #
    wceq
    #
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
    cntzfval.z
    @0
    cM
    cvv
    wcel
    @1
    @11
    wceq
    cM
    cV
    elex
    vm
    cM
    vs
    vm
    cv
    #
    cbs
    cfv
    #
    cpw
    #
    @3
    @4
    @12
    cplusg
    cfv
    #
    co
    #
    @4
    @3
    @15
    co
    #
    wceq
    #
    vy
    @8
    wral
    #
    vx
    @13
    crab
    #
    cmpt
    @11
    cvv
    ccntz
    @12
    cM
    wceq
    #
    vs
    @14
    @20
    @2
    @10
    @21
    @13
    cB
    @21
    @13
    cM
    cbs
    cfv
    #
    cB
    @12
    cM
    cbs
    fveq2
    cntzfval.b
    syl6eqr
    #
    pweqd
    @21
    @19
    @9
    vx
    @13
    cB
    @23
    @21
    @18
    @7
    vy
    @8
    @21
    @16
    @5
    @17
    @6
    @21
    @15
    c.pl
    @3
    @4
    @21
    @15
    cM
    cplusg
    cfv
    c.pl
    @12
    cM
    cplusg
    fveq2
    cntzfval.p
    syl6eqr
    #
    oveqd
    @21
    @15
    c.pl
    @4
    @3
    @24
    oveqd
    eqeq12d
    ralbidv
    rabeqbidv
    mpteq12dv
    vx
    vy
    vm
    vs
    df-cntz
    vs
    @2
    @10
    cB
    cB
    @22
    cvv
    cntzfval.b
    cM
    cbs
    fvex
    eqeltri
    pwex
    mptex
    fvmpt
    syl
    syl5eq
end
