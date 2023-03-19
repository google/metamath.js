include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "cin.mm"
include "ressbas.mm"
include "inss2.mm"
include "syl6eqssr.mm"
include "wn.mm"
include "c0.mm"
include "cress.mm"
include "co.mm"
include "reldmress.mm"
include "ovprc2.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "base0.mm"
include "0ss.mm"
include "eqsstr3i.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"

theorem ressbasss
  let cA: class A
  let cB: class B
  let cR: class R
  let cW: class W
  let va: setvar a
  let vw: setvar w
  assume ressbas.r: |- R = ( W |`s A )
  assume ressbas.b: |- B = ( Base ` W )


  assert |- ( Base ` R ) C_ B

  proof
    cA
    cvv
    wcel
    #
    cR
    cbs
    cfv
    #
    cB
    wss
    @0
    @1
    cA
    cB
    cin
    cB
    cA
    cB
    cR
    cvv
    cW
    ressbas.r
    ressbas.b
    ressbas
    cA
    cB
    inss2
    syl6eqssr
    @0
    wn
    #
    @1
    c0
    cbs
    cfv
    #
    cB
    @2
    cR
    c0
    cbs
    @2
    cR
    cW
    cA
    cress
    co
    c0
    ressbas.r
    cW
    cA
    cress
    reldmress
    ovprc2
    syl5eq
    fveq2d
    @3
    c0
    cB
    base0
    cB
    0ss
    eqsstr3i
    syl6eqss
    pm2.61i
end
