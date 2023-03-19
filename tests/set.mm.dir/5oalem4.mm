include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cph.mm"
include "cin.mm"
include "cmv.mm"
include "eqtr3.mm"
include "5oalem2.mm"
include "sylan2.mm"
include "adantlr.mm"
include "5oalem3.mm"
include "elind.mm"

theorem 5oalem4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  assume 5oalem3.1: |- A e. SH
  assume 5oalem3.2: |- B e. SH
  assume 5oalem3.3: |- C e. SH
  assume 5oalem3.4: |- D e. SH
  assume 5oalem3.5: |- F e. SH
  assume 5oalem3.6: |- G e. SH


  assert |- ( ( ( ( ( x e. A /\ y e. B ) /\ ( z e. C /\ w e. D ) ) /\ ( f e. F /\ g e. G ) ) /\ ( ( x +h y ) = ( f +h g ) /\ ( z +h w ) = ( f +h g ) ) ) -> ( x -h z ) e. ( ( ( A +H C ) i^i ( B +H D ) ) i^i ( ( ( A +H F ) i^i ( B +H G ) ) +H ( ( C +H F ) i^i ( D +H G ) ) ) ) )

  proof
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    #
    cB
    wcel
    wa
    vz
    cv
    #
    cC
    wcel
    vw
    cv
    #
    cD
    wcel
    wa
    wa
    #
    vf
    cv
    #
    cF
    wcel
    vg
    cv
    #
    cG
    wcel
    wa
    #
    wa
    @0
    @1
    cva
    co
    #
    @5
    @6
    cva
    co
    #
    wceq
    @2
    @3
    cva
    co
    #
    @9
    wceq
    wa
    #
    wa
    cA
    cC
    cph
    co
    cB
    cD
    cph
    co
    cin
    #
    cA
    cF
    cph
    co
    cB
    cG
    cph
    co
    cin
    cC
    cF
    cph
    co
    cD
    cG
    cph
    co
    cin
    cph
    co
    @0
    @2
    cmv
    co
    #
    @4
    @11
    @13
    @12
    wcel
    #
    @7
    @11
    @4
    @8
    @10
    wceq
    @14
    @8
    @10
    @9
    eqtr3
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    5oalem3.1
    5oalem3.2
    5oalem3.3
    5oalem3.4
    5oalem2
    sylan2
    adantlr
    vx
    vy
    vz
    vw
    cA
    cB
    cC
    cD
    vf
    vg
    cF
    cG
    5oalem3.1
    5oalem3.2
    5oalem3.3
    5oalem3.4
    5oalem3.5
    5oalem3.6
    5oalem3
    elind
end
