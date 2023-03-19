include "cdm.mm"
include "wcel.mm"
include "wsmo.mm"
include "cfv.mm"
include "con0.mm"
include "wi.mm"
include "wf.mm"
include "word.mm"
include "cv.mm"
include "wral.mm"
include "dfsmo2.mm"
include "simp1bi.mm"
include "ffvelrn.mm"
include "expcom.mm"
include "syl5.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "0elon.mm"
include "syl6eqel.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem smofvon2
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( Smo F -> ( F ` B ) e. On )

  proof
    cB
    cF
    cdm
    #
    wcel
    #
    cF
    wsmo
    #
    cB
    cF
    cfv
    #
    con0
    wcel
    #
    wi
    @2
    @0
    con0
    cF
    wf
    #
    @1
    @4
    @2
    @5
    @0
    word
    vy
    cv
    cF
    cfv
    vx
    cv
    #
    cF
    cfv
    wcel
    vy
    @6
    wral
    vx
    @0
    wral
    vx
    vy
    cF
    dfsmo2
    simp1bi
    @5
    @1
    @4
    @0
    con0
    cB
    cF
    ffvelrn
    expcom
    syl5
    @1
    wn
    #
    @4
    @2
    @7
    @3
    c0
    con0
    cB
    cF
    ndmfv
    0elon
    syl6eqel
    a1d
    pm2.61i
end
