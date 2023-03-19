include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wf1.mm"
include "cz.mm"
include "wcel.mm"
include "ccsh.mm"
include "wceq.mm"
include "w3a.mm"
include "wf.mm"
include "cv.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cword.mm"
include "f1f.mm"
include "iswrdi.mm"
include "syl.mm"
include "cshwf.mm"
include "3adant1.mm"
include "adantr.mm"
include "wb.mm"
include "feq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "dff13.mm"
include "caddc.mm"
include "cmo.mm"
include "fveq1.mm"
include "3ad2ant1.mm"
include "cshwidxmod.mm"
include "3expia.mm"
include "com12.mm"
include "impcom.mm"
include "eqtrd.mm"
include "adantld.mm"
include "imp.mm"
include "eqeq12d.mm"
include "adantlr.mm"
include "cn.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "elfzo0.mm"
include "nn0z.mm"
include "simpl.mm"
include "zaddcld.mm"
include "simpr.mm"
include "jca.mm"
include "ex.mm"
include "3ad2ant3.mm"
include "3adant3.mm"
include "sylbi.mm"
include "zmodfzo.mm"
include "expcom.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "addmodlteq.mm"
include "3expa.mm"
include "ancoms.mm"
include "bicomd.mm"
include "sylibrd.mm"
include "syld.mm"
include "impancom.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "3exp1.mm"
include "com14.mm"
include "3imp1.mm"
include "mpd.mm"
include "3imp.mm"
include "sylibr.mm"

theorem cshf1
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F : ( 0 ..^ ( # ` F ) ) -1-1-> A /\ S e. ZZ /\ G = ( F cyclShift S ) ) -> G : ( 0 ..^ ( # ` F ) ) -1-1-> A )

  proof
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cA
    cF
    wf1
    #
    cS
    cz
    wcel
    #
    cG
    cF
    cS
    ccsh
    co
    #
    wceq
    #
    w3a
    @1
    cA
    cG
    wf
    #
    vi
    cv
    #
    cG
    cfv
    #
    vj
    cv
    #
    cG
    cfv
    #
    wceq
    #
    vi
    vj
    weq
    #
    wi
    #
    vj
    @1
    wral
    vi
    @1
    wral
    #
    wa
    #
    @1
    cA
    cG
    wf1
    @2
    @3
    @5
    @15
    @2
    cF
    cA
    cword
    wcel
    #
    @3
    @5
    @15
    wi
    wi
    @2
    @1
    cA
    cF
    wf
    #
    @16
    @1
    cA
    cF
    f1f
    cA
    @0
    cF
    iswrdi
    syl
    @2
    @16
    @3
    @5
    @15
    @2
    @16
    @3
    w3a
    #
    @5
    wa
    #
    @6
    @14
    @19
    @6
    @1
    cA
    @4
    wf
    #
    @18
    @20
    @5
    @16
    @3
    @20
    @2
    cA
    cS
    cF
    cshwf
    3adant1
    adantr
    @5
    @6
    @20
    wb
    @18
    @1
    cA
    cG
    @4
    feq1
    adantl
    mpbird
    @2
    @16
    @3
    @5
    @14
    @2
    @17
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    @1
    wral
    vx
    @1
    wral
    #
    wa
    @16
    @3
    @5
    @14
    wi
    wi
    wi
    #
    vx
    vy
    @1
    cA
    cF
    dff13
    @28
    @29
    @17
    @5
    @16
    @3
    @28
    @14
    @5
    @16
    @3
    @28
    @14
    @5
    @16
    @3
    w3a
    #
    @28
    wa
    #
    @13
    vi
    vj
    @1
    @1
    @31
    @7
    @1
    wcel
    #
    @9
    @1
    wcel
    #
    wa
    #
    wa
    @11
    @7
    cS
    caddc
    co
    #
    @0
    cmo
    co
    #
    cF
    cfv
    #
    @9
    cS
    caddc
    co
    #
    @0
    cmo
    co
    #
    cF
    cfv
    #
    wceq
    #
    @12
    @30
    @34
    @11
    @41
    wb
    @28
    @30
    @34
    wa
    #
    @8
    @37
    @10
    @40
    @42
    @8
    @7
    @4
    cfv
    #
    @37
    @30
    @8
    @43
    wceq
    #
    @34
    @5
    @16
    @44
    @3
    @7
    cG
    @4
    fveq1
    3ad2ant1
    adantr
    @34
    @30
    @43
    @37
    wceq
    #
    @32
    @30
    @45
    wi
    @33
    @30
    @32
    @45
    @16
    @3
    @32
    @45
    wi
    @5
    @16
    @3
    @32
    @45
    @7
    cS
    cA
    cF
    cshwidxmod
    3expia
    3adant1
    com12
    adantr
    impcom
    eqtrd
    @42
    @10
    @9
    @4
    cfv
    #
    @40
    @30
    @10
    @46
    wceq
    #
    @34
    @5
    @16
    @47
    @3
    @9
    cG
    @4
    fveq1
    3ad2ant1
    adantr
    @30
    @34
    @46
    @40
    wceq
    #
    @30
    @33
    @48
    @32
    @16
    @3
    @33
    @48
    wi
    @5
    @16
    @3
    @33
    @48
    @9
    cS
    cA
    cF
    cshwidxmod
    3expia
    3adant1
    adantld
    imp
    eqtrd
    eqeq12d
    adantlr
    @31
    @34
    @41
    @12
    wi
    #
    @30
    @34
    @28
    @49
    @42
    @28
    @41
    @36
    @39
    wceq
    #
    wi
    #
    @49
    @42
    @36
    @1
    wcel
    #
    @39
    @1
    wcel
    #
    @28
    @51
    wi
    @42
    @35
    cz
    wcel
    #
    @0
    cn
    wcel
    #
    wa
    #
    @52
    @34
    @30
    @56
    @32
    @30
    @56
    wi
    #
    @33
    @32
    @7
    cn0
    wcel
    #
    @55
    @7
    @0
    clt
    wbr
    #
    w3a
    @57
    @7
    @0
    elfzo0
    @58
    @55
    @57
    @59
    @30
    @58
    @55
    wa
    #
    @56
    @3
    @5
    @60
    @56
    wi
    @16
    @3
    @60
    @56
    @3
    @60
    wa
    #
    @54
    @55
    @61
    @7
    cS
    @60
    @7
    cz
    wcel
    #
    @3
    @58
    @62
    @55
    @7
    nn0z
    adantr
    adantl
    @3
    @60
    simpl
    zaddcld
    @60
    @55
    @3
    @58
    @55
    simpr
    adantl
    jca
    ex
    3ad2ant3
    com12
    3adant3
    sylbi
    adantr
    impcom
    @35
    @0
    zmodfzo
    syl
    @42
    @38
    cz
    wcel
    #
    @55
    wa
    #
    @53
    @30
    @34
    @64
    @30
    @33
    @64
    @32
    @3
    @5
    @33
    @64
    wi
    @16
    @33
    @3
    @64
    @33
    @9
    cn0
    wcel
    #
    @55
    @9
    @0
    clt
    wbr
    #
    w3a
    @3
    @64
    wi
    #
    @9
    @0
    elfzo0
    @65
    @55
    @67
    @66
    @3
    @65
    @55
    wa
    #
    @64
    @3
    @68
    wa
    #
    @63
    @55
    @69
    @9
    cS
    @68
    @9
    cz
    wcel
    #
    @3
    @65
    @70
    @55
    @9
    nn0z
    adantr
    adantl
    @3
    @68
    simpl
    zaddcld
    @68
    @55
    @3
    @65
    @55
    simpr
    adantl
    jca
    expcom
    3adant3
    sylbi
    com12
    3ad2ant3
    adantld
    imp
    @38
    @0
    zmodfzo
    syl
    @27
    @51
    @37
    @24
    wceq
    #
    @36
    @23
    wceq
    #
    wi
    vx
    vy
    @36
    @39
    @1
    @1
    @21
    @36
    wceq
    #
    @25
    @71
    @26
    @72
    @73
    @22
    @37
    @24
    @21
    @36
    cF
    fveq2
    eqeq1d
    @21
    @36
    @23
    eqeq1
    imbi12d
    @23
    @39
    wceq
    #
    @71
    @41
    @72
    @50
    @74
    @24
    @40
    @37
    @23
    @39
    cF
    fveq2
    eqeq2d
    @23
    @39
    @36
    eqeq2
    imbi12d
    rspc2v
    syl2anc
    @42
    @51
    @49
    @42
    @51
    wa
    @41
    @50
    @12
    @42
    @51
    simpr
    @42
    @12
    @50
    wb
    #
    @51
    @30
    @34
    @75
    @3
    @5
    @34
    @75
    wi
    @16
    @3
    @34
    @75
    @3
    @34
    wa
    @50
    @12
    @34
    @3
    @50
    @12
    wb
    #
    @32
    @33
    @3
    @76
    cS
    @7
    @9
    @0
    addmodlteq
    3expa
    ancoms
    bicomd
    ex
    3ad2ant3
    imp
    adantr
    sylibrd
    ex
    syld
    impancom
    imp
    sylbid
    ralrimivva
    3exp1
    com14
    adantl
    sylbi
    3imp1
    jca
    3exp1
    mpd
    3imp
    vi
    vj
    @1
    cA
    cG
    dff13
    sylibr
end
