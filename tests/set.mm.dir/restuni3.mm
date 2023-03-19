include "crest.mm"
include "co.mm"
include "cuni.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "eluni2.mm"
include "biimpi.mm"
include "adantl.mm"
include "wi.mm"
include "w3a.mm"
include "wceq.mm"
include "simpr.mm"
include "wb.mm"
include "elrest.mm"
include "syl2anc.mm"
include "adantr.mm"
include "mpbid.mm"
include "3adant3.mm"
include "simpl.mm"
include "eleqtrd.mm"
include "ex.mm"
include "3ad2ant3.mm"
include "reximdv.mm"
include "mpd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "elinel1.mm"
include "elunii.mm"
include "elinel2.mm"
include "elind.mm"
include "rexlimdva.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "sylib.mm"
include "eqid.mm"
include "elrestd.mm"
include "3adant1r.mm"
include "simp3.mm"
include "simp1r.mm"
include "syl.mm"
include "eleq2.mm"
include "rspcev.mm"
include "eqssd.mm"

theorem restuni3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume restuni3.1: |- ( ph -> A e. V )
  assume restuni3.2: |- ( ph -> B e. W )


  assert |- ( ph -> U. ( A |`t B ) = ( U. A i^i B ) )

  proof
    wph
    cA
    cB
    crest
    co
    #
    cuni
    #
    cA
    cuni
    #
    cB
    cin
    #
    wph
    vx
    cv
    #
    @3
    wcel
    #
    vx
    @1
    wral
    @1
    @3
    wss
    wph
    @5
    vx
    @1
    wph
    @4
    @1
    wcel
    #
    wa
    #
    @4
    vz
    cv
    #
    cB
    cin
    #
    wcel
    #
    vz
    cA
    wrex
    #
    @5
    @7
    @4
    vy
    cv
    #
    wcel
    #
    vy
    @0
    wrex
    #
    @11
    @6
    @14
    wph
    @6
    @14
    vy
    @4
    @0
    eluni2
    #
    biimpi
    adantl
    wph
    @14
    @11
    wi
    @6
    wph
    @13
    @11
    vy
    @0
    wph
    @12
    @0
    wcel
    #
    @13
    @11
    wph
    @16
    @13
    w3a
    #
    @12
    @9
    wceq
    #
    vz
    cA
    wrex
    #
    @11
    wph
    @16
    @19
    @13
    wph
    @16
    wa
    @16
    @19
    wph
    @16
    simpr
    wph
    @16
    @19
    wb
    #
    @16
    wph
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    @20
    restuni3.1
    restuni3.2
    vz
    @12
    cB
    cA
    cV
    cW
    elrest
    syl2anc
    adantr
    mpbid
    3adant3
    @17
    @18
    @10
    vz
    cA
    @13
    wph
    @18
    @10
    wi
    @16
    @13
    @18
    @10
    @13
    @18
    wa
    @4
    @12
    @9
    @13
    @18
    simpl
    @13
    @18
    simpr
    eleqtrd
    ex
    3ad2ant3
    reximdv
    mpd
    3exp
    rexlimdv
    adantr
    mpd
    @7
    @10
    @5
    vz
    cA
    @8
    cA
    wcel
    #
    @10
    @5
    wi
    @7
    @23
    @10
    @5
    @23
    @10
    wa
    #
    @2
    cB
    @4
    @24
    @4
    @8
    wcel
    #
    @23
    @4
    @2
    wcel
    #
    @10
    @25
    @23
    @4
    @8
    cB
    elinel1
    adantl
    @23
    @10
    simpl
    @4
    @8
    cA
    elunii
    syl2anc
    @10
    @4
    cB
    wcel
    #
    @23
    @4
    @8
    cB
    elinel2
    adantl
    elind
    ex
    adantl
    rexlimdva
    mpd
    ralrimiva
    vx
    @1
    @3
    dfss3
    sylibr
    wph
    @6
    vx
    @3
    wral
    @3
    @1
    wss
    wph
    @6
    vx
    @3
    wph
    @5
    wa
    #
    @14
    @6
    @28
    @25
    vz
    cA
    wrex
    #
    @14
    @5
    @29
    wph
    @5
    @26
    @29
    @4
    @2
    cB
    elinel1
    vz
    @4
    cA
    eluni2
    sylib
    adantl
    @28
    @25
    @14
    vz
    cA
    @28
    @23
    @25
    @14
    @28
    @23
    @25
    w3a
    #
    @9
    @0
    wcel
    #
    @10
    @14
    wph
    @23
    @25
    @31
    @5
    wph
    @23
    @31
    @25
    wph
    @23
    wa
    @9
    cB
    cA
    cV
    cW
    @8
    wph
    @21
    @23
    restuni3.1
    adantr
    wph
    @22
    @23
    restuni3.2
    adantr
    wph
    @23
    simpr
    @9
    eqid
    elrestd
    3adant3
    3adant1r
    @30
    @25
    @27
    @10
    @28
    @23
    @25
    simp3
    @30
    @5
    @27
    wph
    @5
    @23
    @25
    simp1r
    @4
    @2
    cB
    elinel2
    syl
    @25
    @27
    wa
    @8
    cB
    @4
    @25
    @27
    simpl
    @25
    @27
    simpr
    elind
    syl2anc
    @13
    @10
    vy
    @9
    @0
    @12
    @9
    @4
    eleq2
    rspcev
    syl2anc
    3exp
    rexlimdv
    mpd
    @15
    sylibr
    ralrimiva
    vx
    @3
    @1
    dfss3
    sylibr
    eqssd
end
