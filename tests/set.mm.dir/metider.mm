include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cmetid.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "metidss.mm"
include "xpss.mm"
include "syl6ss.mm"
include "df-rel.mm"
include "sylibr.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "ssbrd.mm"
include "imp.mm"
include "brxp.mm"
include "sylib.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "psmetsym.mm"
include "3expb.mm"
include "eqeq1d.mm"
include "metidv.mm"
include "wb.mm"
include "ancom2s.mm"
include "3bitr4d.mm"
include "biimpd.mm"
include "impancom.mm"
include "mpd.mm"
include "cle.mm"
include "cxad.mm"
include "simpl.mm"
include "simprr.mm"
include "syldan.mm"
include "simpld.mm"
include "simprl.mm"
include "simprd.mm"
include "psmettri2.mm"
include "syl13anc.mm"
include "mpbid.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "cxr.mm"
include "0xr.mm"
include "xaddid1.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "breqtrd.mm"
include "psmetge0.mm"
include "syl3anc.mm"
include "psmetcl.mm"
include "xrletri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "syl12anc.mm"
include "mpbird.mm"
include "psmet0.mm"
include "anabsan2.mm"
include "impbida.mm"
include "iserd.mm"

theorem metider
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( D e. ( PsMet ` X ) -> ( ~Met ` D ) Er X )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    vx
    vy
    vz
    cX
    cD
    cmetid
    cfv
    #
    @0
    @1
    cvv
    cvv
    cxp
    #
    wss
    @1
    wrel
    @0
    @1
    cX
    cX
    cxp
    #
    @2
    cD
    cX
    metidss
    #
    cX
    cX
    xpss
    syl6ss
    @1
    df-rel
    sylibr
    @0
    vx
    cv
    #
    vy
    cv
    #
    @1
    wbr
    #
    wa
    #
    @5
    cX
    wcel
    #
    @6
    cX
    wcel
    #
    wa
    #
    @6
    @5
    @1
    wbr
    #
    @8
    @5
    @6
    @3
    wbr
    #
    @11
    @0
    @7
    @13
    @0
    @1
    @3
    @5
    @6
    @4
    ssbrd
    imp
    @5
    @6
    cX
    cX
    brxp
    sylib
    #
    @0
    @11
    @7
    @12
    @0
    @11
    wa
    #
    @7
    @12
    @15
    @5
    @6
    cD
    co
    #
    cc0
    wceq
    #
    @6
    @5
    cD
    co
    #
    cc0
    wceq
    #
    @7
    @12
    @15
    @16
    @18
    cc0
    @0
    @9
    @10
    @16
    @18
    wceq
    #
    @5
    @6
    cD
    cX
    psmetsym
    3expb
    #
    eqeq1d
    @5
    @6
    cD
    cX
    metidv
    #
    @0
    @10
    @9
    @12
    @19
    wb
    @6
    @5
    cD
    cX
    metidv
    ancom2s
    3bitr4d
    biimpd
    impancom
    mpd
    @0
    @7
    @6
    vz
    cv
    #
    @1
    wbr
    #
    wa
    #
    wa
    #
    @5
    @23
    @1
    wbr
    #
    @5
    @23
    cD
    co
    #
    cc0
    wceq
    #
    @26
    @29
    @28
    cc0
    cle
    wbr
    #
    cc0
    @28
    cle
    wbr
    #
    @26
    @28
    @18
    @6
    @23
    cD
    co
    #
    cxad
    co
    #
    cc0
    cle
    @26
    @0
    @10
    @9
    @23
    cX
    wcel
    #
    @28
    @33
    cle
    wbr
    @0
    @25
    simpl
    #
    @26
    @10
    @34
    @0
    @25
    @24
    @10
    @34
    wa
    #
    @0
    @7
    @24
    simprr
    #
    @0
    @24
    wa
    @6
    @23
    @3
    wbr
    #
    @36
    @0
    @24
    @38
    @0
    @1
    @3
    @6
    @23
    @4
    ssbrd
    imp
    @6
    @23
    cX
    cX
    brxp
    sylib
    syldan
    #
    simpld
    @26
    @9
    @10
    @0
    @25
    @7
    @11
    @0
    @7
    @24
    simprl
    #
    @14
    syldan
    #
    simpld
    #
    @26
    @10
    @34
    @39
    simprd
    #
    @5
    @23
    @6
    cD
    cX
    psmettri2
    syl13anc
    @26
    @33
    cc0
    cc0
    cxad
    co
    #
    cc0
    @26
    @18
    cc0
    @32
    cc0
    cxad
    @26
    @16
    @18
    cc0
    @0
    @25
    @11
    @20
    @41
    @21
    syldan
    @26
    @7
    @17
    @40
    @0
    @25
    @11
    @7
    @17
    wb
    @41
    @22
    syldan
    mpbid
    eqtr3d
    @26
    @24
    @32
    cc0
    wceq
    #
    @37
    @0
    @25
    @36
    @24
    @45
    wb
    @39
    @6
    @23
    cD
    cX
    metidv
    syldan
    mpbid
    oveq12d
    cc0
    cxr
    wcel
    #
    @44
    cc0
    wceq
    0xr
    cc0
    xaddid1
    ax-mp
    syl6eq
    breqtrd
    @26
    @0
    @9
    @34
    @31
    @35
    @42
    @43
    @5
    @23
    cD
    cX
    psmetge0
    syl3anc
    @26
    @28
    cxr
    wcel
    #
    @46
    @29
    @30
    @31
    wa
    wb
    @26
    @0
    @9
    @34
    @47
    @35
    @42
    @43
    @5
    @23
    cD
    cX
    psmetcl
    syl3anc
    0xr
    @28
    cc0
    xrletri3
    sylancl
    mpbir2and
    @26
    @0
    @9
    @34
    @27
    @29
    wb
    @35
    @42
    @43
    @5
    @23
    cD
    cX
    metidv
    syl12anc
    mpbird
    @0
    @9
    @5
    @5
    @1
    wbr
    #
    @0
    @9
    wa
    @48
    @5
    @5
    cD
    co
    cc0
    wceq
    #
    @5
    cD
    cX
    psmet0
    @0
    @9
    @48
    @49
    wb
    @5
    @5
    cD
    cX
    metidv
    anabsan2
    mpbird
    @0
    @48
    wa
    #
    @9
    @9
    @50
    @5
    @5
    @3
    wbr
    #
    @9
    @9
    wa
    @0
    @48
    @51
    @0
    @1
    @3
    @5
    @5
    @4
    ssbrd
    imp
    @5
    @5
    cX
    cX
    brxp
    sylib
    simpld
    impbida
    iserd
end
