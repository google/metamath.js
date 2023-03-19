include "cspr.mm"
include "cfv.mm"
include "wss.mm"
include "cpr.mm"
include "wcel.mm"
include "wa.mm"
include "ssel2.mm"
include "prsprel.mm"
include "stoic3.mm"

theorem prsssprel
  let cP: class P
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( P C_ ( Pairs ` V ) /\ { X , Y } e. P /\ ( X e. U /\ Y e. W ) ) -> ( X e. V /\ Y e. V ) )

  proof
    cP
    cV
    cspr
    cfv
    #
    wss
    cX
    cY
    cpr
    #
    cP
    wcel
    @1
    @0
    wcel
    cX
    cU
    wcel
    cY
    cW
    wcel
    wa
    cX
    cV
    wcel
    cY
    cV
    wcel
    wa
    cP
    @0
    @1
    ssel2
    cU
    cV
    cW
    cX
    cY
    prsprel
    stoic3
end
