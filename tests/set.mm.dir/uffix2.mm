include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cint.mm"
include "wex.mm"
include "cpw.mm"
include "crab.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "cuni.mm"
include "cfil.mm"
include "wss.mm"
include "ufilfil.mm"
include "filn0.mm"
include "intssuni.mm"
include "3syl.mm"
include "filunibas.mm"
include "syl.mm"
include "sseqtrd.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "uffixfr.mm"
include "anbi2d.mm"
include "bitrd.mm"
include "exbidv.mm"
include "n0.mm"
include "df-rex.mm"
include "3bitr4g.mm"

theorem uffix2
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cX: class X
  let cA: class A

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X x
  disjoint X y
  disjoint A x
  assert |- ( F e. ( UFil ` X ) -> ( |^| F =/= (/) <-> E. x e. X F = { y e. ~P X | x e. y } ) )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    vx
    cv
    #
    cF
    cint
    #
    wcel
    #
    vx
    wex
    @1
    cX
    wcel
    #
    cF
    @1
    vy
    cv
    wcel
    vy
    cX
    cpw
    crab
    wceq
    #
    wa
    #
    vx
    wex
    @2
    c0
    wne
    @5
    vx
    cX
    wrex
    @0
    @3
    @6
    vx
    @0
    @3
    @4
    @3
    wa
    @6
    @0
    @3
    @4
    @0
    @2
    cX
    @1
    @0
    @2
    cF
    cuni
    #
    cX
    @0
    cF
    cX
    cfil
    cfv
    wcel
    #
    cF
    c0
    wne
    @2
    @7
    wss
    cF
    cX
    ufilfil
    #
    cF
    cX
    filn0
    cF
    intssuni
    3syl
    @0
    @8
    @7
    cX
    wceq
    @9
    cF
    cX
    filunibas
    syl
    sseqtrd
    sseld
    pm4.71rd
    @0
    @3
    @5
    @4
    vy
    @1
    cF
    cX
    uffixfr
    anbi2d
    bitrd
    exbidv
    vx
    @2
    n0
    @5
    vx
    cX
    df-rex
    3bitr4g
end
