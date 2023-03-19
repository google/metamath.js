include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "n0i.mm"
include "wn.mm"
include "cbs.mm"
include "cfv.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "base0.mm"
include "3eqtr4g.mm"
include "nsyl2.mm"

theorem elbasfv
  let cB: class B
  let cS: class S
  let cF: class F
  let cX: class X
  let cZ: class Z
  assume elbasfv.s: |- S = ( F ` Z )
  assume elbasfv.b: |- B = ( Base ` S )


  assert |- ( X e. B -> Z e. _V )

  proof
    cX
    cB
    wcel
    cB
    c0
    wceq
    cZ
    cvv
    wcel
    #
    cB
    cX
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
    cZ
    cF
    cfv
    c0
    elbasfv.s
    cZ
    cF
    fvprc
    syl5eq
    fveq2d
    elbasfv.b
    base0
    3eqtr4g
    nsyl2
end
