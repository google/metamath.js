include "ctop.mm"
include "wcel.mm"
include "ckgen.mm"
include "cfv.mm"
include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "cin.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "elssuni.mm"
include "a1i.mm"
include "elrestr.mm"
include "3expa.mm"
include "an32s.mm"
include "a1d.mm"
include "ralrimiva.mm"
include "ex.mm"
include "jcad.mm"
include "ctopon.mm"
include "wb.mm"
include "eqid.mm"
include "toptopon.mm"
include "elkgen.mm"
include "sylbi.mm"
include "sylibrd.mm"
include "ssrdv.mm"

theorem kgenss
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let cK: class K


  assert |- ( J e. Top -> J C_ ( kGen ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    vx
    cJ
    cJ
    ckgen
    cfv
    #
    @0
    vx
    cv
    #
    cJ
    wcel
    #
    @2
    cJ
    cuni
    #
    wss
    #
    cJ
    vk
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    @2
    @6
    cin
    @7
    wcel
    #
    wi
    #
    vk
    @4
    cpw
    #
    wral
    #
    wa
    #
    @2
    @1
    wcel
    #
    @0
    @3
    @5
    @12
    @3
    @5
    wi
    @0
    @2
    cJ
    elssuni
    a1i
    @0
    @3
    @12
    @0
    @3
    wa
    #
    @10
    vk
    @11
    @15
    @6
    @11
    wcel
    #
    wa
    @9
    @8
    @0
    @16
    @3
    @9
    @0
    @16
    @3
    @9
    @2
    @6
    cJ
    ctop
    @11
    elrestr
    3expa
    an32s
    a1d
    ralrimiva
    ex
    jcad
    @0
    cJ
    @4
    ctopon
    cfv
    wcel
    @14
    @13
    wb
    cJ
    @4
    @4
    eqid
    toptopon
    @2
    vk
    cJ
    @4
    elkgen
    sylbi
    sylibrd
    ssrdv
end
