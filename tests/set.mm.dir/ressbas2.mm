include "wss.mm"
include "cin.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "df-ss.mm"
include "biimpi.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "ressbas.mm"
include "syl.mm"
include "eqtr3d.mm"

theorem ressbas2
  let cA: class A
  let cB: class B
  let cR: class R
  let cW: class W
  let va: setvar a
  let vw: setvar w
  assume ressbas.r: |- R = ( W |`s A )
  assume ressbas.b: |- B = ( Base ` W )


  assert |- ( A C_ B -> A = ( Base ` R ) )

  proof
    cA
    cB
    wss
    #
    cA
    cB
    cin
    #
    cA
    cR
    cbs
    cfv
    #
    @0
    @1
    cA
    wceq
    cA
    cB
    df-ss
    biimpi
    @0
    cA
    cvv
    wcel
    @1
    @2
    wceq
    cA
    cB
    cB
    cW
    cbs
    cfv
    cvv
    ressbas.b
    cW
    cbs
    fvex
    eqeltri
    ssex
    cA
    cB
    cR
    cvv
    cW
    ressbas.r
    ressbas.b
    ressbas
    syl
    eqtr3d
end
