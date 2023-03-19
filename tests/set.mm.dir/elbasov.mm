include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wa.mm"
include "n0i.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "co.mm"
include "ovprc.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "base0.mm"
include "3eqtr4g.mm"
include "nsyl2.mm"

theorem elbasov
  let cA: class A
  let cB: class B
  let cS: class S
  let cO: class O
  let cX: class X
  let cY: class Y
  assume elbasov.o: |- Rel dom O
  assume elbasov.s: |- S = ( X O Y )
  assume elbasov.b: |- B = ( Base ` S )


  assert |- ( A e. B -> ( X e. _V /\ Y e. _V ) )

  proof
    cA
    cB
    wcel
    cB
    c0
    wceq
    cX
    cvv
    wcel
    cY
    cvv
    wcel
    wa
    #
    cB
    cA
    n0i
    @0
    wn
    #
    cS
    cbs
    cfv
    c0
    cbs
    cfv
    cB
    c0
    @1
    cS
    c0
    cbs
    @1
    cS
    cX
    cY
    cO
    co
    c0
    elbasov.s
    cX
    cY
    cO
    elbasov.o
    ovprc
    syl5eq
    fveq2d
    elbasov.b
    base0
    3eqtr4g
    nsyl2
end
