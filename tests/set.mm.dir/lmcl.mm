include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "clm.mm"
include "wbr.mm"
include "wa.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "cv.mm"
include "cres.mm"
include "wf.mm"
include "cuz.mm"
include "crn.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "id.mm"
include "lmbr.mm"
include "biimpa.mm"
include "simp2d.mm"

theorem lmcl
  let cP: class P
  let cF: class F
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vy: setvar y


  assert |- ( ( J e. ( TopOn ` X ) /\ F ( ~~>t ` J ) P ) -> P e. X )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cP
    cJ
    clm
    cfv
    wbr
    #
    wa
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    cP
    cX
    wcel
    #
    cP
    vu
    cv
    #
    wcel
    vy
    cv
    #
    @4
    cF
    @5
    cres
    wf
    vy
    cuz
    crn
    wrex
    wi
    vu
    cJ
    wral
    #
    @0
    @1
    @2
    @3
    @6
    w3a
    @0
    vy
    vu
    cP
    cF
    cJ
    cX
    @0
    id
    lmbr
    biimpa
    simp2d
end
