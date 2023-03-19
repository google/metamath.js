include "cen.mm"
include "wbr.mm"
include "cwdom.mm"
include "id.mm"
include "cdom.mm"
include "endom.mm"
include "domwdom.mm"
include "syl.mm"
include "wdomtr.mm"
include "syl2anr.mm"
include "ensym.mm"
include "3syl.mm"
include "impbida.mm"

theorem wdomen2
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


  assert |- ( A ~~ B -> ( C ~<_* A <-> C ~<_* B ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cC
    cA
    cwdom
    wbr
    #
    cC
    cB
    cwdom
    wbr
    #
    @1
    @1
    cA
    cB
    cwdom
    wbr
    #
    @2
    @0
    @1
    id
    @0
    cA
    cB
    cdom
    wbr
    @3
    cA
    cB
    endom
    cA
    cB
    domwdom
    syl
    cC
    cA
    cB
    wdomtr
    syl2anr
    @2
    @2
    cB
    cA
    cwdom
    wbr
    #
    @1
    @0
    @2
    id
    @0
    cB
    cA
    cen
    wbr
    cB
    cA
    cdom
    wbr
    @4
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
    cC
    cB
    cA
    wdomtr
    syl2anr
    impbida
end
