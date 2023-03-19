include "ccmp.mm"
include "cfn.mm"
include "ccref.mm"
include "cv.mm"
include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cref.mm"
include "wbr.mm"
include "wss.mm"
include "simplr.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "elpwi.mm"
include "syl.mm"
include "ad4antlr.mm"
include "sstrd.mm"
include "selpw.mm"
include "sylibr.mm"
include "simprd.mm"
include "elind.mm"
include "simpr.mm"
include "simpllr.mm"
include "eqtr3d.mm"
include "eqid.mm"
include "ssref.mm"
include "syl3anc.mm"
include "breq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "r19.29an.mm"
include "wf.mm"
include "cfv.mm"
include "wex.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "isref.mm"
include "ax-mp.mm"
include "simprbi.mm"
include "adantl.mm"
include "sseq2.mm"
include "ac6sg.mm"
include "sylc.mm"
include "crn.mm"
include "frn.mm"
include "rnex.mm"
include "elpw.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfi.mm"
include "rnfi.mm"
include "simp-5r.mm"
include "refbas.mm"
include "ad3antlr.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "rspa.mm"
include "adantll.mm"
include "sseld.mm"
include "ex.mm"
include "reximdai.mm"
include "eluni2.mm"
include "a1i.mm"
include "fnunirn.mm"
include "3imtr4d.mm"
include "ssrdv.mm"
include "eqsstrd.mm"
include "unissd.mm"
include "eqssd.mm"
include "eqtrd.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "expl.mm"
include "exlimdv.mm"
include "mpd.mm"
include "impbida.mm"
include "pm5.74da.mm"
include "ralbidva.mm"
include "pm5.32i.mm"
include "iscmp.mm"
include "iscref.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem cmpcref
  let vf: setvar f
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Comp = CovHasRef Fin

  proof
    vj
    ccmp
    cfn
    ccref
    #
    vj
    cv
    #
    ctop
    wcel
    #
    @1
    cuni
    #
    vy
    cv
    #
    cuni
    #
    wceq
    #
    @3
    vx
    cv
    #
    cuni
    #
    wceq
    #
    vx
    @4
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vy
    @1
    cpw
    #
    wral
    #
    wa
    @2
    @6
    vz
    cv
    #
    @4
    cref
    wbr
    #
    vz
    @14
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vy
    @14
    wral
    #
    wa
    @1
    ccmp
    wcel
    @1
    @0
    wcel
    @2
    @15
    @21
    @2
    @13
    @20
    vy
    @14
    @2
    @4
    @14
    wcel
    #
    wa
    #
    @6
    @12
    @19
    @23
    @6
    wa
    #
    @12
    @19
    @24
    @9
    @19
    vx
    @11
    @24
    @7
    @11
    wcel
    #
    wa
    #
    @9
    wa
    #
    @7
    @18
    wcel
    @7
    @4
    cref
    wbr
    #
    @19
    @27
    @14
    cfn
    @7
    @27
    @7
    @1
    wss
    @7
    @14
    wcel
    #
    @27
    @7
    @4
    @1
    @27
    @7
    @10
    wcel
    #
    @7
    @4
    wss
    #
    @27
    @30
    @7
    cfn
    wcel
    #
    @27
    @25
    @30
    @32
    wa
    @24
    @25
    @9
    simplr
    @7
    @10
    cfn
    elin
    sylib
    #
    simpld
    @7
    @4
    elpwi
    syl
    #
    @22
    @4
    @1
    wss
    @2
    @6
    @25
    @9
    @4
    @1
    elpwi
    ad4antlr
    sstrd
    vx
    @1
    selpw
    sylibr
    #
    @27
    @30
    @32
    @33
    simprd
    elind
    @27
    @29
    @31
    @8
    @5
    wceq
    @28
    @35
    @34
    @27
    @3
    @8
    @5
    @26
    @9
    simpr
    @23
    @6
    @25
    @9
    simpllr
    eqtr3d
    @7
    @4
    @14
    @8
    @5
    @8
    eqid
    @5
    eqid
    #
    ssref
    syl3anc
    @17
    @28
    vz
    @7
    @18
    @16
    @7
    @4
    cref
    breq1
    rspcev
    syl2anc
    r19.29an
    @24
    @17
    @12
    vz
    @18
    @24
    @16
    @18
    wcel
    #
    wa
    #
    @17
    wa
    #
    @16
    @4
    vf
    cv
    #
    wf
    #
    vu
    cv
    #
    @42
    @40
    cfv
    #
    wss
    #
    vu
    @16
    wral
    #
    wa
    #
    vf
    wex
    #
    @12
    @39
    @37
    @42
    vv
    cv
    #
    wss
    #
    vv
    @4
    wrex
    vu
    @16
    wral
    #
    @47
    @24
    @37
    @17
    simplr
    @17
    @50
    @38
    @17
    @5
    @16
    cuni
    #
    wceq
    #
    @50
    @16
    cvv
    wcel
    @17
    @52
    @50
    wa
    wb
    vz
    vex
    vu
    vv
    @16
    @4
    cvv
    @51
    @5
    @51
    eqid
    #
    @36
    isref
    ax-mp
    simprbi
    adantl
    @49
    @44
    vu
    vv
    @16
    @4
    vf
    @18
    @48
    @43
    @42
    sseq2
    ac6sg
    sylc
    @39
    @46
    @12
    vf
    @39
    @41
    @45
    @12
    @39
    @41
    wa
    #
    @45
    wa
    #
    @40
    crn
    #
    @11
    wcel
    @3
    @56
    cuni
    #
    wceq
    #
    @12
    @55
    @10
    cfn
    @56
    @55
    @56
    @4
    wss
    #
    @56
    @10
    wcel
    @55
    @41
    @59
    @39
    @41
    @45
    simplr
    #
    @16
    @4
    @40
    frn
    syl
    #
    @56
    @4
    @40
    vf
    vex
    rnex
    elpw
    sylibr
    @55
    @40
    cfn
    wcel
    #
    @56
    cfn
    wcel
    @55
    @40
    @16
    wfn
    #
    @16
    cfn
    wcel
    #
    @62
    @55
    @41
    @63
    @60
    @16
    @4
    @40
    ffn
    syl
    #
    @37
    @64
    @24
    @17
    @41
    @45
    @37
    @16
    @14
    wcel
    @64
    @16
    @14
    cfn
    elin
    simprbi
    ad4antlr
    @16
    @40
    fnfi
    syl2anc
    @40
    rnfi
    syl
    elind
    @55
    @3
    @5
    @57
    @23
    @6
    @37
    @17
    @41
    @45
    simp-5r
    @55
    @5
    @57
    @55
    @5
    @51
    @57
    @17
    @52
    @38
    @41
    @45
    @16
    @4
    @51
    @5
    @53
    @36
    refbas
    ad3antlr
    @55
    vx
    @51
    @57
    @55
    @7
    @42
    wcel
    #
    vu
    @16
    wrex
    #
    @7
    @43
    wcel
    #
    vu
    @16
    wrex
    #
    @7
    @51
    wcel
    #
    @7
    @57
    wcel
    #
    @55
    @66
    @68
    vu
    @16
    @54
    @45
    vu
    @54
    vu
    nfv
    @44
    vu
    @16
    nfra1
    nfan
    @55
    @42
    @16
    wcel
    #
    @66
    @68
    wi
    @55
    @72
    wa
    @42
    @43
    @7
    @45
    @72
    @44
    @54
    @44
    vu
    @16
    rspa
    adantll
    sseld
    ex
    reximdai
    @70
    @67
    wb
    @55
    vu
    @7
    @16
    eluni2
    a1i
    @55
    @63
    @71
    @69
    wb
    @65
    vu
    @7
    @40
    @16
    fnunirn
    syl
    3imtr4d
    ssrdv
    eqsstrd
    @55
    @56
    @4
    @61
    unissd
    eqssd
    eqtrd
    @9
    @58
    vx
    @56
    @11
    @7
    @56
    wceq
    @8
    @57
    @3
    @7
    @56
    unieq
    eqeq2d
    rspcev
    syl2anc
    expl
    exlimdv
    mpd
    r19.29an
    impbida
    pm5.74da
    ralbidva
    pm5.32i
    vy
    vx
    @1
    @3
    @3
    eqid
    #
    iscmp
    vy
    vz
    cfn
    @1
    @3
    @73
    iscref
    3bitr4i
    eqriv
end
