include "clly.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ctop.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "llytop.mm"
include "resttop.mm"
include "sylan.mm"
include "wss.mm"
include "wb.mm"
include "restopn2.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp3.mm"
include "llyi.mm"
include "syl3anc.mm"
include "simprl.mm"
include "simprr1.mm"
include "simpl2r.mm"
include "sstrd.mm"
include "syl.mm"
include "adantr.mm"
include "simpl1r.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "selpw.mm"
include "sylibr.mm"
include "elind.mm"
include "simprr2.mm"
include "wceq.mm"
include "restabs.mm"
include "simprr3.mm"
include "eqeltrd.mm"
include "jca32.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "islly.mm"
include "sylanbrc.mm"

theorem llyrest
  let cA: class A
  let cB: class B
  let cJ: class J
  let vj: setvar j
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( J e. Locally A /\ B e. J ) -> ( J |`t B ) e. Locally A )

  proof
    cJ
    cA
    clly
    #
    wcel
    #
    cB
    cJ
    wcel
    #
    wa
    #
    cJ
    cB
    crest
    co
    #
    ctop
    wcel
    #
    vy
    cv
    #
    vv
    cv
    #
    wcel
    #
    @4
    @7
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vv
    @4
    vx
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @12
    wral
    #
    vx
    @4
    wral
    @4
    @0
    wcel
    @1
    cJ
    ctop
    wcel
    #
    @2
    @5
    cA
    cJ
    llytop
    #
    cB
    cJ
    cJ
    resttop
    sylan
    @3
    @16
    vx
    @4
    @3
    @12
    @4
    wcel
    #
    @12
    cJ
    wcel
    #
    @12
    cB
    wss
    #
    wa
    #
    @16
    @1
    @17
    @2
    @19
    @22
    wb
    @18
    cB
    @12
    cJ
    restopn2
    sylan
    @3
    @22
    @16
    @3
    @22
    wa
    @15
    vy
    @12
    @3
    @22
    @6
    @12
    wcel
    #
    @15
    @3
    @22
    @23
    w3a
    #
    @7
    @12
    wss
    #
    @8
    cJ
    @7
    crest
    co
    #
    cA
    wcel
    #
    w3a
    #
    vv
    cJ
    wrex
    #
    @15
    @24
    @1
    @20
    @23
    @29
    @1
    @2
    @22
    @23
    simp1l
    #
    @3
    @20
    @21
    @23
    simp2l
    @3
    @22
    @23
    simp3
    vv
    cA
    @6
    @12
    cJ
    llyi
    syl3anc
    @24
    @28
    @11
    vv
    cJ
    @14
    @24
    @7
    cJ
    wcel
    #
    @28
    wa
    #
    @7
    @14
    wcel
    #
    @11
    wa
    @24
    @32
    wa
    #
    @33
    @8
    @10
    @34
    @4
    @13
    @7
    @34
    @7
    @4
    wcel
    #
    @31
    @7
    cB
    wss
    #
    @24
    @31
    @28
    simprl
    @34
    @7
    @12
    cB
    @25
    @8
    @27
    @31
    @24
    simprr1
    #
    @20
    @21
    @3
    @23
    @32
    simpl2r
    sstrd
    #
    @34
    @17
    @2
    @35
    @31
    @36
    wa
    wb
    @24
    @17
    @32
    @24
    @1
    @17
    @30
    @18
    syl
    adantr
    #
    @1
    @2
    @22
    @23
    @32
    simpl1r
    #
    cB
    @7
    cJ
    restopn2
    syl2anc
    mpbir2and
    @34
    @25
    @7
    @13
    wcel
    @37
    vv
    @12
    selpw
    sylibr
    elind
    @25
    @8
    @27
    @31
    @24
    simprr2
    @34
    @9
    @26
    cA
    @34
    @17
    @36
    @2
    @9
    @26
    wceq
    @39
    @38
    @40
    @7
    cB
    cJ
    ctop
    cJ
    restabs
    syl3anc
    @25
    @8
    @27
    @31
    @24
    simprr3
    eqeltrd
    jca32
    ex
    reximdv2
    mpd
    3expa
    ralrimiva
    ex
    sylbid
    ralrimiv
    vx
    vy
    vv
    cA
    @4
    islly
    sylanbrc
end
