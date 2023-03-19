include "con0.mm"
include "wcel.mm"
include "ccf.mm"
include "cfv.mm"
include "wss.mm"
include "ccrd.mm"
include "cflecard.mm"
include "cardonle.mm"
include "syl5ss.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "wceq.mm"
include "cff.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"

theorem cfle
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- ( cf ` A ) C_ A

  proof
    cA
    con0
    wcel
    #
    cA
    ccf
    cfv
    #
    cA
    wss
    @0
    @1
    cA
    ccrd
    cfv
    cA
    cA
    cflecard
    cA
    cardonle
    syl5ss
    @0
    wn
    @1
    c0
    cA
    @0
    cA
    ccf
    cdm
    #
    wcel
    @1
    c0
    wceq
    @2
    con0
    cA
    con0
    con0
    ccf
    cff
    fdmi
    eleq2i
    cA
    ccf
    ndmfv
    sylnbir
    cA
    0ss
    syl6eqss
    pm2.61i
end
