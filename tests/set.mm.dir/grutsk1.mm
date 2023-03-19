include "ctsk.mm"
include "wcel.mm"
include "wtr.mm"
include "wa.mm"
include "cgru.mm"
include "cv.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "crn.mm"
include "cuni.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "simpr.mm"
include "tskpw.mm"
include "adantlr.mm"
include "tskpr.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "wf.mm"
include "wb.mm"
include "elmapg.mm"
include "tskurn.mm"
include "3expia.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "3jca.mm"
include "elgrug.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem grutsk1
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( T e. Tarski /\ Tr T ) -> T e. Univ )

  proof
    cT
    ctsk
    wcel
    #
    cT
    wtr
    #
    wa
    #
    cT
    cgru
    wcel
    #
    @1
    vx
    cv
    #
    cpw
    cT
    wcel
    #
    @4
    vy
    cv
    #
    cpr
    cT
    wcel
    #
    vy
    cT
    wral
    #
    @6
    crn
    cuni
    cT
    wcel
    #
    vy
    cT
    @4
    cmap
    co
    #
    wral
    #
    w3a
    #
    vx
    cT
    wral
    #
    @0
    @1
    simpr
    @2
    @12
    vx
    cT
    @2
    @4
    cT
    wcel
    #
    wa
    #
    @5
    @8
    @11
    @0
    @14
    @5
    @1
    @4
    cT
    tskpw
    adantlr
    @0
    @14
    @8
    @1
    @0
    @14
    wa
    @7
    vy
    cT
    @0
    @14
    @6
    cT
    wcel
    @7
    @4
    @6
    cT
    tskpr
    3expa
    ralrimiva
    adantlr
    @15
    @9
    vy
    @10
    @15
    @6
    @10
    wcel
    #
    @4
    cT
    @6
    wf
    #
    @9
    @0
    @14
    @16
    @17
    wb
    @1
    cT
    @4
    @6
    ctsk
    cT
    elmapg
    adantlr
    @2
    @14
    @17
    @9
    @4
    cT
    @6
    tskurn
    3expia
    sylbid
    ralrimiv
    3jca
    ralrimiva
    @0
    @3
    @1
    @13
    wa
    wb
    @1
    vx
    vy
    cT
    ctsk
    elgrug
    adantr
    mpbir2and
end
