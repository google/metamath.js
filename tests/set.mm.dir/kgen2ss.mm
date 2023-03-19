include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "ckgen.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "cin.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "cuni.mm"
include "simp1.mm"
include "elpwi.mm"
include "resttopon.mm"
include "syl2an.mm"
include "wceq.mm"
include "simp2.mm"
include "toponuni.mm"
include "syl.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "ctop.mm"
include "simpl2.mm"
include "topontop.mm"
include "simpl3.mm"
include "ssrest.mm"
include "syl2anc.mm"
include "eqid.mm"
include "sscmp.mm"
include "3com23.mm"
include "3expia.mm"
include "sseld.mm"
include "imim12d.mm"
include "ralimdva.mm"
include "anim2d.mm"
include "wb.mm"
include "elkgen.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem kgen2ss
  let cJ: class J
  let cK: class K
  let cX: class X
  let vg: setvar g
  let vk: setvar k
  let vx: setvar x
  let vz: setvar z
  let cF: class F
  let cY: class Y


  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` X ) /\ J C_ K ) -> ( kGen ` J ) C_ ( kGen ` K ) )

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
    #
    vx
    cJ
    ckgen
    cfv
    #
    cK
    ckgen
    cfv
    #
    @4
    vx
    cv
    #
    cX
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
    @7
    @9
    cin
    #
    @10
    wcel
    #
    wi
    #
    vk
    cX
    cpw
    #
    wral
    #
    wa
    #
    @8
    cK
    @9
    crest
    co
    #
    ccmp
    wcel
    #
    @12
    @18
    wcel
    #
    wi
    #
    vk
    @15
    wral
    #
    wa
    #
    @7
    @5
    wcel
    #
    @7
    @6
    wcel
    #
    @4
    @16
    @22
    @8
    @4
    @14
    @21
    vk
    @15
    @4
    @9
    @15
    wcel
    #
    wa
    #
    @19
    @11
    @13
    @20
    @27
    @10
    @18
    cuni
    #
    ctopon
    cfv
    #
    wcel
    #
    @10
    @18
    wss
    #
    @19
    @11
    wi
    @27
    @10
    @9
    ctopon
    cfv
    #
    @29
    @4
    @1
    @9
    cX
    wss
    #
    @10
    @32
    wcel
    @26
    @1
    @2
    @3
    simp1
    @9
    cX
    elpwi
    #
    @9
    cJ
    cX
    resttopon
    syl2an
    @27
    @9
    @28
    ctopon
    @27
    @18
    @32
    wcel
    #
    @9
    @28
    wceq
    @4
    @2
    @33
    @35
    @26
    @1
    @2
    @3
    simp2
    @34
    @9
    cK
    cX
    resttopon
    syl2an
    @9
    @18
    toponuni
    syl
    fveq2d
    eleqtrd
    @27
    cK
    ctop
    wcel
    #
    @3
    @31
    @27
    @2
    @36
    @1
    @2
    @3
    @26
    simpl2
    cX
    cK
    topontop
    syl
    @1
    @2
    @3
    @26
    simpl3
    @9
    cJ
    cK
    ctop
    ssrest
    syl2anc
    #
    @30
    @31
    @19
    @11
    @30
    @19
    @31
    @11
    @10
    @18
    @28
    @28
    eqid
    sscmp
    3com23
    3expia
    syl2anc
    @27
    @10
    @18
    @12
    @37
    sseld
    imim12d
    ralimdva
    anim2d
    @1
    @2
    @24
    @17
    wb
    @3
    @7
    vk
    cJ
    cX
    elkgen
    3ad2ant1
    @2
    @1
    @25
    @23
    wb
    @3
    @7
    vk
    cK
    cX
    elkgen
    3ad2ant2
    3imtr4d
    ssrdv
end
