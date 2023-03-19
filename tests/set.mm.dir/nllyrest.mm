include "cnlly.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ctop.mm"
include "cv.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "nllytop.mm"
include "resttop.mm"
include "sylan.mm"
include "wss.mm"
include "wb.mm"
include "restopn2.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp3.mm"
include "nlly2i.mm"
include "syl3anc.mm"
include "cuni.mm"
include "3ad2ant1.mm"
include "simp3l.mm"
include "simp3r2.mm"
include "simp2.mm"
include "elpwid.mm"
include "simp12r.mm"
include "sstrd.mm"
include "syl.mm"
include "simp11r.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "simp3r1.mm"
include "opnneip.mm"
include "wceq.mm"
include "elssuni.mm"
include "eqid.mm"
include "restuni.mm"
include "sseqtrd.mm"
include "ssnei2.mm"
include "syl22anc.mm"
include "elind.mm"
include "restabs.mm"
include "simp3r3.mm"
include "eqeltrd.mm"
include "jca.mm"
include "3expa.mm"
include "rexlimdvaa.mm"
include "expimpd.mm"
include "reximdv2.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "isnlly.mm"
include "sylanbrc.mm"

theorem nllyrest
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


  assert |- ( ( J e. N-Locally A /\ B e. J ) -> ( J |`t B ) e. N-Locally A )

  proof
    cJ
    cA
    cnlly
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
    @4
    vs
    cv
    #
    crest
    co
    #
    cA
    wcel
    #
    vs
    vy
    cv
    #
    csn
    #
    @4
    cnei
    cfv
    cfv
    #
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
    nllytop
    #
    cB
    cJ
    cJ
    resttop
    sylan
    #
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
    @20
    @23
    wb
    @18
    cB
    @12
    cJ
    restopn2
    sylan
    @3
    @23
    @16
    @3
    @23
    wa
    @15
    vy
    @12
    @3
    @23
    @9
    @12
    wcel
    #
    @15
    @3
    @23
    @24
    w3a
    #
    @9
    vu
    cv
    #
    wcel
    #
    @26
    @6
    wss
    #
    cJ
    @6
    crest
    co
    #
    cA
    wcel
    #
    w3a
    #
    vu
    cJ
    wrex
    #
    vs
    @13
    wrex
    #
    @15
    @25
    @1
    @21
    @24
    @33
    @1
    @2
    @23
    @24
    simp1l
    #
    @3
    @21
    @22
    @24
    simp2l
    @3
    @23
    @24
    simp3
    vu
    cA
    @9
    @12
    cJ
    vs
    nlly2i
    syl3anc
    @25
    @32
    @8
    vs
    @13
    @14
    @25
    @6
    @13
    wcel
    #
    @32
    @6
    @14
    wcel
    #
    @8
    wa
    #
    @25
    @35
    wa
    @31
    @37
    vu
    cJ
    @25
    @35
    @26
    cJ
    wcel
    #
    @31
    wa
    #
    @37
    @25
    @35
    @39
    w3a
    #
    @36
    @8
    @40
    @11
    @13
    @6
    @40
    @5
    @26
    @11
    wcel
    #
    @28
    @6
    @4
    cuni
    #
    wss
    @6
    @11
    wcel
    @25
    @35
    @5
    @39
    @3
    @23
    @5
    @24
    @19
    3ad2ant1
    3ad2ant1
    #
    @40
    @5
    @26
    @4
    wcel
    #
    @27
    @41
    @43
    @40
    @44
    @38
    @26
    cB
    wss
    #
    @25
    @35
    @38
    @31
    simp3l
    @40
    @26
    @6
    cB
    @27
    @28
    @30
    @38
    @25
    @35
    simp3r2
    #
    @40
    @6
    @12
    cB
    @40
    @6
    @12
    @25
    @35
    @39
    simp2
    #
    elpwid
    @21
    @22
    @3
    @24
    @35
    @39
    simp12r
    sstrd
    #
    sstrd
    @40
    @17
    @2
    @44
    @38
    @45
    wa
    wb
    @40
    @1
    @17
    @25
    @35
    @1
    @39
    @34
    3ad2ant1
    @18
    syl
    #
    @1
    @2
    @23
    @24
    @35
    @39
    simp11r
    #
    cB
    @26
    cJ
    restopn2
    syl2anc
    mpbir2and
    @27
    @28
    @30
    @38
    @25
    @35
    simp3r1
    @9
    @4
    @26
    opnneip
    syl3anc
    @46
    @40
    @6
    cB
    @42
    @48
    @40
    @17
    cB
    cJ
    cuni
    #
    wss
    #
    cB
    @42
    wceq
    @49
    @40
    @2
    @52
    @50
    cB
    cJ
    elssuni
    syl
    cB
    cJ
    @51
    @51
    eqid
    restuni
    syl2anc
    sseqtrd
    @10
    @4
    @6
    @26
    @42
    @42
    eqid
    ssnei2
    syl22anc
    @47
    elind
    @40
    @7
    @29
    cA
    @40
    @17
    @6
    cB
    wss
    @2
    @7
    @29
    wceq
    @49
    @48
    @50
    @6
    cB
    cJ
    ctop
    cJ
    restabs
    syl3anc
    @27
    @28
    @30
    @38
    @25
    @35
    simp3r3
    eqeltrd
    jca
    3expa
    rexlimdvaa
    expimpd
    reximdv2
    mpd
    3expa
    ralrimiva
    ex
    sylbid
    ralrimiv
    vx
    vy
    vs
    cA
    @4
    isnlly
    sylanbrc
end
