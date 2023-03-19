include "wfun.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "wmo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "eqtr3.mm"
include "ad2ant2l.mm"
include "gen2.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "mo4.mm"
include "mpbir.mm"
include "funoprab.mm"
include "cmpt2.mm"
include "df-mpt2.mm"
include "eqtri.mm"
include "funeqi.mm"

theorem mpt2fun
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vw: setvar w
  let vz: setvar z
  assume mpt2fun.1: |- F = ( x e. A , y e. B |-> C )

  disjoint x y
  disjoint A w
  disjoint A z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint C w
  disjoint C z
  disjoint w x
  disjoint x z
  disjoint w y
  disjoint y z
  assert |- Fun F

  proof
    cF
    wfun
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    #
    vz
    cv
    #
    cC
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    #
    wfun
    @3
    vx
    vy
    vz
    @3
    vz
    wmo
    @3
    @0
    vw
    cv
    #
    cC
    wceq
    #
    wa
    #
    wa
    vz
    vw
    weq
    #
    wi
    #
    vw
    wal
    vz
    wal
    @9
    vz
    vw
    @2
    @6
    @8
    @0
    @0
    @1
    @5
    cC
    eqtr3
    ad2ant2l
    gen2
    @3
    @7
    vz
    vw
    @8
    @2
    @6
    @0
    @1
    @5
    cC
    eqeq1
    anbi2d
    mo4
    mpbir
    funoprab
    cF
    @4
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    @4
    mpt2fun.1
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    eqtri
    funeqi
    mpbir
end
