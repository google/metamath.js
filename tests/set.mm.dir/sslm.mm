include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "cres.mm"
include "wf.mm"
include "cuz.mm"
include "crn.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "copab.mm"
include "clm.mm"
include "idd.mm"
include "ssralv.mm"
include "3anim123d.mm"
include "ssopab2dv.mm"
include "3ad2ant3.mm"
include "wceq.mm"
include "lmfval.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "3sstr4d.mm"

theorem sslm
  let cJ: class J
  let cK: class K
  let cX: class X
  let vf: setvar f
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` X ) /\ J C_ K ) -> ( ~~>t ` K ) C_ ( ~~>t ` J ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cK
    @0
    wcel
    #
    cJ
    cK
    wss
    #
    w3a
    vf
    cv
    #
    cX
    cc
    cpm
    co
    wcel
    #
    vx
    cv
    #
    cX
    wcel
    #
    @6
    vu
    cv
    #
    wcel
    vy
    cv
    #
    @8
    @4
    @9
    cres
    wf
    vy
    cuz
    crn
    wrex
    wi
    #
    vu
    cK
    wral
    #
    w3a
    #
    vf
    vx
    copab
    #
    @5
    @7
    @10
    vu
    cJ
    wral
    #
    w3a
    #
    vf
    vx
    copab
    #
    cK
    clm
    cfv
    #
    cJ
    clm
    cfv
    #
    @3
    @1
    @13
    @16
    wss
    @2
    @3
    @12
    @15
    vf
    vx
    @3
    @5
    @5
    @7
    @7
    @11
    @14
    @3
    @5
    idd
    @3
    @7
    idd
    @10
    vu
    cJ
    cK
    ssralv
    3anim123d
    ssopab2dv
    3ad2ant3
    @2
    @1
    @17
    @13
    wceq
    @3
    vx
    vy
    vu
    vf
    cK
    cX
    lmfval
    3ad2ant2
    @1
    @2
    @18
    @16
    wceq
    @3
    vx
    vy
    vu
    vf
    cJ
    cX
    lmfval
    3ad2ant1
    3sstr4d
end
