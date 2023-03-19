include "wcel.mm"
include "cvv.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "cpclN.mm"
include "cfv.mm"
include "catm.mm"
include "cpsubsp.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "rabeqdv.mm"
include "inteqd.mm"
include "mpteq12dv.mm"
include "df-pclN.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem pclfvalN
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S
  let cU: class U
  let cK: class K
  let cV: class V
  let vk: setvar k
  let cX: class X
  assume pclfval.a: |- A = ( Atoms ` K )
  assume pclfval.s: |- S = ( PSubSp ` K )
  assume pclfval.c: |- U = ( PCl ` K )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint K x
  disjoint K y
  disjoint S x
  disjoint S y
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint K k
  disjoint S k
  disjoint X x
  disjoint X y
  assert |- ( K e. V -> U = ( x e. ~P A |-> |^| { y e. S | x C_ y } ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    #
    cU
    vx
    cA
    cpw
    #
    vx
    cv
    vy
    cv
    wss
    #
    vy
    cS
    crab
    #
    cint
    #
    cmpt
    #
    wceq
    cK
    cV
    elex
    @0
    cU
    cK
    cpclN
    cfv
    @5
    pclfval.c
    vk
    cK
    vx
    vk
    cv
    #
    catm
    cfv
    #
    cpw
    #
    @2
    vy
    @6
    cpsubsp
    cfv
    #
    crab
    #
    cint
    #
    cmpt
    @5
    cvv
    cpclN
    @6
    cK
    wceq
    #
    vx
    @8
    @11
    @1
    @4
    @12
    @7
    cA
    @12
    @7
    cK
    catm
    cfv
    #
    cA
    @6
    cK
    catm
    fveq2
    pclfval.a
    syl6eqr
    pweqd
    @12
    @10
    @3
    @12
    @2
    vy
    @9
    cS
    @12
    @9
    cK
    cpsubsp
    cfv
    cS
    @6
    cK
    cpsubsp
    fveq2
    pclfval.s
    syl6eqr
    rabeqdv
    inteqd
    mpteq12dv
    vx
    vy
    vk
    df-pclN
    vx
    @1
    @4
    cA
    cA
    @13
    cvv
    pclfval.a
    cK
    catm
    fvex
    eqeltri
    pwex
    mptex
    fvmpt
    syl5eq
    syl
end
