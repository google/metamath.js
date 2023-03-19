include "cen.mm"
include "wbr.mm"
include "cwdom.mm"
include "cdom.mm"
include "ensym.mm"
include "endom.mm"
include "domwdom.mm"
include "3syl.mm"
include "wdomtr.mm"
include "sylan.mm"
include "syl.mm"
include "impbida.mm"

theorem wdomen1
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cY: class Y
  let cF: class F
  let cZ: class Z


  assert |- ( A ~~ B -> ( A ~<_* C <-> B ~<_* C ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    cC
    cwdom
    wbr
    #
    cB
    cC
    cwdom
    wbr
    #
    @0
    cB
    cA
    cwdom
    wbr
    #
    @1
    @2
    @0
    cB
    cA
    cen
    wbr
    cB
    cA
    cdom
    wbr
    @3
    cA
    cB
    ensym
    cB
    cA
    endom
    cB
    cA
    domwdom
    3syl
    cB
    cA
    cC
    wdomtr
    sylan
    @0
    cA
    cB
    cwdom
    wbr
    #
    @2
    @1
    @0
    cA
    cB
    cdom
    wbr
    @4
    cA
    cB
    endom
    cA
    cB
    domwdom
    syl
    cA
    cB
    cC
    wdomtr
    sylan
    impbida
end
