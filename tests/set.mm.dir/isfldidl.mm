include "cfld.mm"
include "wcel.mm"
include "ccring.mm"
include "wne.mm"
include "cidl.mm"
include "cfv.mm"
include "csn.mm"
include "cpr.mm"
include "wceq.mm"
include "w3a.mm"
include "fldcrng.mm"
include "cdrng.mm"
include "flddivrng.mm"
include "dvrunz.mm"
include "syl.mm"
include "divrngidl.mm"
include "3jca.mm"
include "crngo.mm"
include "cv.mm"
include "co.mm"
include "wrex.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "crngorngo.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "crab.mm"
include "crn.mm"
include "c1st.mm"
include "rneqi.mm"
include "eqtri.mm"
include "rngo1cl.mm"
include "ad2antrr.mm"
include "cigen.mm"
include "wn.mm"
include "eldif.mm"
include "wss.mm"
include "snssi.mm"
include "igenss.mm"
include "sylan2.mm"
include "vex.mm"
include "snss.mm"
include "biimpri.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "con3dimp.mm"
include "sylan.mm"
include "anasss.mm"
include "sylan2b.mm"
include "adantlr.mm"
include "wo.mm"
include "eldifi.mm"
include "snssd.mm"
include "igenidl.mm"
include "imp.mm"
include "an32s.mm"
include "ovex.mm"
include "elpr.mm"
include "sylib.mm"
include "ord.mm"
include "mpd.mm"
include "sylanl1.mm"
include "prnc.mm"
include "eqtr3d.mm"
include "eleqtrd.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "simprd.mm"
include "eqcom.mm"
include "rexbii.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "3adant2.mm"
include "jca32.mm"
include "isdrngo3.mm"
include "simp1.mm"
include "isfld2.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem isfldidl
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume isfldidl.1: |- G = ( 1st ` K )
  assume isfldidl.2: |- H = ( 2nd ` K )
  assume isfldidl.3: |- X = ran G
  assume isfldidl.4: |- Z = ( GId ` G )
  assume isfldidl.5: |- U = ( GId ` H )


  assert |- ( K e. Fld <-> ( K e. CRingOps /\ U =/= Z /\ ( Idl ` K ) = { { Z } , X } ) )

  proof
    cK
    cfld
    wcel
    #
    cK
    ccring
    wcel
    #
    cU
    cZ
    wne
    #
    cK
    cidl
    cfv
    #
    cZ
    csn
    #
    cX
    cpr
    #
    wceq
    #
    w3a
    #
    @0
    @1
    @2
    @6
    cK
    fldcrng
    @0
    cK
    cdrng
    wcel
    #
    @2
    cK
    flddivrng
    #
    cK
    cU
    cG
    cH
    cX
    cZ
    isfldidl.1
    isfldidl.2
    isfldidl.3
    isfldidl.4
    isfldidl.5
    dvrunz
    syl
    @0
    @8
    @6
    @9
    cK
    cG
    cH
    cX
    cZ
    isfldidl.1
    isfldidl.2
    isfldidl.3
    isfldidl.4
    divrngidl
    syl
    3jca
    @7
    @8
    @1
    @0
    @7
    cK
    crngo
    wcel
    #
    @2
    vy
    cv
    vx
    cv
    #
    cH
    co
    #
    cU
    wceq
    #
    vy
    cX
    wrex
    #
    vx
    cX
    @4
    cdif
    #
    wral
    #
    wa
    wa
    @8
    @7
    @10
    @2
    @16
    @1
    @2
    @10
    @6
    cK
    crngorngo
    #
    3ad2ant1
    @1
    @2
    @6
    simp2
    @1
    @6
    @16
    @2
    @1
    @6
    wa
    #
    @14
    vx
    @15
    @18
    @11
    @15
    wcel
    #
    wa
    #
    cU
    @12
    wceq
    #
    vy
    cX
    wrex
    #
    @14
    @20
    cU
    cX
    wcel
    #
    @22
    @20
    cU
    vz
    cv
    #
    @12
    wceq
    #
    vy
    cX
    wrex
    #
    vz
    cX
    crab
    #
    wcel
    @23
    @22
    wa
    @20
    cU
    cX
    @27
    @1
    @23
    @6
    @19
    @1
    @10
    @23
    @17
    cK
    cU
    cH
    cX
    cX
    cG
    crn
    cK
    c1st
    cfv
    #
    crn
    isfldidl.3
    cG
    @28
    isfldidl.1
    rneqi
    eqtri
    isfldidl.2
    isfldidl.5
    rngo1cl
    syl
    ad2antrr
    @20
    cK
    @11
    csn
    #
    cigen
    co
    #
    cX
    @27
    @1
    @10
    @6
    @19
    @30
    cX
    wceq
    #
    @17
    @10
    @6
    wa
    @19
    wa
    #
    @30
    @4
    wceq
    #
    wn
    #
    @31
    @10
    @19
    @34
    @6
    @19
    @10
    @11
    cX
    wcel
    #
    @11
    @4
    wcel
    #
    wn
    #
    wa
    @34
    @11
    cX
    @4
    eldif
    @10
    @35
    @37
    @34
    @10
    @35
    wa
    @29
    @30
    wss
    #
    @37
    @34
    @35
    @10
    @29
    cX
    wss
    #
    @38
    @11
    cX
    snssi
    cK
    @29
    cG
    cX
    isfldidl.1
    isfldidl.3
    igenss
    sylan2
    @38
    @33
    @36
    @38
    @11
    @30
    wcel
    #
    @33
    @36
    @40
    @38
    @11
    @30
    vx
    vex
    snss
    biimpri
    @30
    @4
    @11
    eleq2
    syl5ibcom
    con3dimp
    sylan
    anasss
    sylan2b
    adantlr
    @32
    @33
    @31
    @32
    @30
    @5
    wcel
    #
    @33
    @31
    wo
    @10
    @19
    @6
    @41
    @10
    @19
    wa
    #
    @6
    @41
    @42
    @30
    @3
    wcel
    #
    @6
    @41
    @19
    @10
    @39
    @43
    @19
    @11
    cX
    @11
    cX
    @4
    eldifi
    #
    snssd
    cK
    @29
    cG
    cX
    isfldidl.1
    isfldidl.3
    igenidl
    sylan2
    @3
    @5
    @30
    eleq2
    syl5ibcom
    imp
    an32s
    @30
    @4
    cX
    cK
    @29
    cigen
    ovex
    elpr
    sylib
    ord
    mpd
    sylanl1
    @1
    @19
    @30
    @27
    wceq
    #
    @6
    @19
    @1
    @35
    @45
    @44
    vz
    vy
    @11
    cK
    cG
    cH
    cX
    isfldidl.1
    isfldidl.2
    isfldidl.3
    prnc
    sylan2
    adantlr
    eqtr3d
    eleqtrd
    @26
    @22
    vz
    cU
    cX
    @24
    cU
    wceq
    @25
    @21
    vy
    cX
    @24
    cU
    @12
    eqeq1
    rexbidv
    elrab
    sylib
    simprd
    @13
    @21
    vy
    cX
    @12
    cU
    eqcom
    rexbii
    sylibr
    ralrimiva
    3adant2
    jca32
    vx
    vy
    cK
    cU
    cG
    cH
    cX
    cZ
    isfldidl.1
    isfldidl.2
    isfldidl.4
    isfldidl.3
    isfldidl.5
    isdrngo3
    sylibr
    @1
    @2
    @6
    simp1
    cK
    isfld2
    sylanbrc
    impbii
end
