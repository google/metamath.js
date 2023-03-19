include "wrel.mm"
include "cop.mm"
include "ctpos.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "reltpos.mm"
include "a1i.mm"
include "brrelex2.mm"
include "sylan.mm"
include "brtpos.mm"
include "pm5.21nd.mm"

theorem relbrtpos
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( Rel F -> ( <. A , B >. tpos F C <-> <. B , A >. F C ) )

  proof
    cF
    wrel
    #
    cA
    cB
    cop
    #
    cC
    cF
    ctpos
    #
    wbr
    #
    cB
    cA
    cop
    #
    cC
    cF
    wbr
    cC
    cvv
    wcel
    #
    @0
    @2
    wrel
    #
    @3
    @5
    @6
    @0
    cF
    reltpos
    a1i
    @1
    cC
    @2
    brrelex2
    sylan
    @4
    cC
    cF
    brrelex2
    cA
    cB
    cC
    cF
    cvv
    brtpos
    pm5.21nd
end
