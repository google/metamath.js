include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cint.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "rint0.mm"
include "adantl.mm"
include "mre1cl.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "wne.mm"
include "w3a.mm"
include "cpw.mm"
include "simp2.mm"
include "mresspw.mm"
include "3ad2ant1.mm"
include "sstrd.mm"
include "simp3.mm"
include "rintn0.mm"
include "syl2anc.mm"
include "mreintcl.mm"
include "3expa.mm"
include "pm2.61dane.mm"

theorem mrerintcl
  let cC: class C
  let cS: class S
  let cX: class X
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x
  let cI: class I
  let vy: setvar y


  assert |- ( ( C e. ( Moore ` X ) /\ S C_ C ) -> ( X i^i |^| S ) e. C )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cS
    cC
    wss
    #
    wa
    #
    cX
    cS
    cint
    #
    cin
    #
    cC
    wcel
    #
    cS
    c0
    @2
    cS
    c0
    wceq
    #
    wa
    @4
    cX
    cC
    @6
    @4
    cX
    wceq
    @2
    cX
    cS
    rint0
    adantl
    @0
    cX
    cC
    wcel
    @1
    @6
    cC
    cX
    mre1cl
    ad2antrr
    eqeltrd
    @0
    @1
    cS
    c0
    wne
    #
    @5
    @0
    @1
    @7
    w3a
    #
    @4
    @3
    cC
    @8
    cS
    cX
    cpw
    #
    wss
    @7
    @4
    @3
    wceq
    @8
    cS
    cC
    @9
    @0
    @1
    @7
    simp2
    @0
    @1
    cC
    @9
    wss
    @7
    cC
    cX
    mresspw
    3ad2ant1
    sstrd
    @0
    @1
    @7
    simp3
    cX
    cS
    rintn0
    syl2anc
    cC
    cS
    cX
    mreintcl
    eqeltrd
    3expa
    pm2.61dane
end
