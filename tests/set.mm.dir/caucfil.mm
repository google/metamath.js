include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cdm.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cima.mm"
include "cca.mm"
include "ccfil.mm"
include "wa.mm"
include "wi.mm"
include "df-3an.mm"
include "uztrn2.mm"
include "adantll.mm"
include "wceq.mm"
include "simpll3.mm"
include "fdm.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "ffvelrnd.mm"
include "jca.mm"
include "biantrurd.mm"
include "wss.mm"
include "uzss.mm"
include "adantl.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"
include "ralbidv2.mm"
include "bitr3d.mm"
include "syl5bb.mm"
include "ralbidva.mm"
include "r19.26-2.mm"
include "weq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "ralbii.mm"
include "eleq2d.mm"
include "oveq1d.mm"
include "cbvral2v.mm"
include "ralcom.mm"
include "3bitr3i.mm"
include "anbi2i.mm"
include "anidm.mm"
include "3bitr2i.mm"
include "simpll1.mm"
include "ad2ant2l.mm"
include "adantrr.mm"
include "xmetsym.mm"
include "syl3anc.mm"
include "imbi2d.mm"
include "anbi2d.mm"
include "wo.mm"
include "jaob.mm"
include "wb.mm"
include "eluzelz.mm"
include "uztric.mm"
include "syl2an.mm"
include "pm5.5.mm"
include "syl5bbr.mm"
include "bitrd.mm"
include "2ralbidva.mm"
include "rexbidva.mm"
include "wfn.mm"
include "cpw.mm"
include "uzf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "rexima.mm"
include "mp2an.mm"
include "syl6bbr.mm"
include "ralbidv.mm"
include "cc.mm"
include "cpm.mm"
include "cvv.mm"
include "elfvdm.mm"
include "adantr.mm"
include "cnex.mm"
include "jctir.mm"
include "zsscn.mm"
include "sstri.mm"
include "jctr.mm"
include "elpm2r.mm"
include "simpl.mm"
include "simpr.mm"
include "iscau3.mm"
include "baibd.mm"
include "syldan.mm"
include "3impa.mm"
include "cfm.mm"
include "eleq1i.mm"
include "cfbas.mm"
include "uzfbas.mm"
include "fmcfil.mm"
include "syl3an2.mm"
include "3bitr4d.mm"

theorem caucfil
  let cD: class D
  let cF: class F
  let cL: class L
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vu: setvar u
  let vx: setvar x
  assume caucfil.1: |- Z = ( ZZ>= ` M )
  assume caucfil.2: |- L = ( ( X FilMap F ) ` ( ZZ>= " Z ) )


  assert |- ( ( D e. ( *Met ` X ) /\ M e. ZZ /\ F : Z --> X ) -> ( F e. ( Cau ` D ) <-> L e. ( CauFil ` D ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cM
    cz
    wcel
    #
    cZ
    cX
    cF
    wf
    #
    w3a
    #
    vk
    cv
    #
    cF
    cdm
    #
    wcel
    #
    @4
    cF
    cfv
    #
    cX
    wcel
    #
    @7
    vm
    cv
    #
    cF
    cfv
    #
    cD
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vm
    @4
    cuz
    cfv
    #
    wral
    #
    w3a
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @13
    vm
    vu
    cv
    #
    wral
    #
    vk
    @22
    wral
    #
    vu
    cuz
    cZ
    cima
    #
    wrex
    #
    vx
    crp
    wral
    #
    cF
    cD
    cca
    cfv
    wcel
    #
    cL
    cD
    ccfil
    cfv
    #
    wcel
    #
    @3
    @20
    @26
    vx
    crp
    @3
    @20
    @13
    vm
    @18
    wral
    #
    vk
    @18
    wral
    #
    vj
    cZ
    wrex
    #
    @26
    @3
    @19
    @32
    vj
    cZ
    @3
    @17
    cZ
    wcel
    #
    wa
    #
    @19
    @9
    @14
    wcel
    #
    @13
    wi
    #
    vm
    @18
    wral
    #
    vk
    @18
    wral
    #
    @32
    @35
    @16
    @38
    vk
    @18
    @16
    @6
    @8
    wa
    #
    @15
    wa
    #
    @35
    @4
    @18
    wcel
    #
    wa
    #
    @38
    @6
    @8
    @15
    df-3an
    @43
    @15
    @41
    @38
    @43
    @40
    @15
    @43
    @6
    @8
    @43
    @4
    cZ
    @5
    @34
    @42
    @4
    cZ
    wcel
    @3
    cM
    @4
    @17
    cZ
    caucfil.1
    uztrn2
    adantll
    #
    @43
    @2
    @5
    cZ
    wceq
    @0
    @1
    @2
    @34
    @42
    simpll3
    #
    cZ
    cX
    cF
    fdm
    syl
    eleqtrrd
    @43
    cZ
    cX
    @4
    cF
    @45
    @44
    ffvelrnd
    #
    jca
    biantrurd
    @43
    @13
    @37
    vm
    @14
    @18
    @43
    @37
    @9
    @18
    wcel
    #
    @36
    wa
    #
    @13
    wi
    @47
    @37
    wi
    @43
    @36
    @48
    @13
    @43
    @36
    @47
    @43
    @14
    @18
    @9
    @42
    @14
    @18
    wss
    @35
    @17
    @4
    uzss
    adantl
    sseld
    pm4.71rd
    imbi1d
    @47
    @36
    @13
    impexp
    syl6bb
    ralbidv2
    bitr3d
    syl5bb
    ralbidva
    @39
    @37
    @4
    @9
    cuz
    cfv
    #
    wcel
    #
    @10
    @7
    cD
    co
    #
    @12
    clt
    wbr
    #
    wi
    #
    wa
    #
    vm
    @18
    wral
    vk
    @18
    wral
    #
    @35
    @32
    @55
    @39
    @53
    vm
    @18
    wral
    vk
    @18
    wral
    #
    wa
    @39
    @39
    wa
    @39
    @37
    @53
    vk
    vm
    @18
    @18
    r19.26-2
    @39
    @56
    @39
    @22
    @49
    wcel
    #
    @10
    @22
    cF
    cfv
    #
    cD
    co
    #
    @12
    clt
    wbr
    #
    wi
    #
    vu
    @18
    wral
    #
    vm
    @18
    wral
    @53
    vk
    @18
    wral
    #
    vm
    @18
    wral
    @39
    @56
    @62
    @63
    vm
    @18
    @61
    @53
    vu
    vk
    @18
    vu
    vk
    weq
    #
    @57
    @50
    @60
    @52
    @22
    @4
    @49
    eleq1
    @64
    @59
    @51
    @12
    clt
    @64
    @58
    @7
    @10
    cD
    @22
    @4
    cF
    fveq2
    oveq2d
    breq1d
    imbi12d
    cbvralv
    ralbii
    @61
    @37
    @22
    @14
    wcel
    #
    @7
    @58
    cD
    co
    #
    @12
    clt
    wbr
    #
    wi
    vm
    vu
    vk
    vm
    @18
    @18
    vm
    vk
    weq
    #
    @57
    @65
    @60
    @67
    @68
    @49
    @14
    @22
    @9
    @4
    cuz
    fveq2
    eleq2d
    @68
    @59
    @66
    @12
    clt
    @68
    @10
    @7
    @58
    cD
    @9
    @4
    cF
    fveq2
    oveq1d
    breq1d
    imbi12d
    vu
    vm
    weq
    #
    @65
    @36
    @67
    @13
    @22
    @9
    @14
    eleq1
    @69
    @66
    @11
    @12
    clt
    @69
    @58
    @10
    @7
    cD
    @22
    @9
    cF
    fveq2
    oveq2d
    breq1d
    imbi12d
    cbvral2v
    @53
    vm
    vk
    @18
    @18
    ralcom
    3bitr3i
    anbi2i
    @39
    anidm
    3bitr2i
    @35
    @54
    @13
    vk
    vm
    @18
    @18
    @35
    @42
    @47
    wa
    #
    wa
    #
    @54
    @37
    @50
    @13
    wi
    #
    wa
    #
    @13
    @71
    @53
    @72
    @37
    @71
    @52
    @13
    @50
    @71
    @51
    @11
    @12
    clt
    @71
    @0
    @10
    cX
    wcel
    @8
    @51
    @11
    wceq
    @0
    @1
    @2
    @34
    @70
    simpll1
    @71
    cZ
    cX
    @9
    cF
    @0
    @1
    @2
    @34
    @70
    simpll3
    @34
    @47
    @9
    cZ
    wcel
    @3
    @42
    cM
    @9
    @17
    cZ
    caucfil.1
    uztrn2
    ad2ant2l
    ffvelrnd
    @35
    @42
    @8
    @47
    @46
    adantrr
    @10
    @7
    cD
    cX
    xmetsym
    syl3anc
    breq1d
    imbi2d
    anbi2d
    @73
    @36
    @50
    wo
    #
    @13
    wi
    #
    @71
    @13
    @36
    @13
    @50
    jaob
    @71
    @74
    @75
    @13
    wb
    @70
    @74
    @35
    @42
    @4
    cz
    wcel
    @9
    cz
    wcel
    @74
    @47
    @17
    @4
    eluzelz
    @17
    @9
    eluzelz
    @4
    @9
    uztric
    syl2an
    adantl
    @74
    @13
    pm5.5
    syl
    syl5bbr
    bitrd
    2ralbidva
    syl5bbr
    bitrd
    rexbidva
    cuz
    cz
    wfn
    #
    cZ
    cz
    wss
    @26
    @33
    wb
    cz
    cz
    cpw
    #
    cuz
    wf
    @76
    uzf
    cz
    @77
    cuz
    ffn
    ax-mp
    cZ
    cM
    cuz
    cfv
    cz
    caucfil.1
    cM
    uzssz
    eqsstri
    #
    @24
    @32
    vu
    vj
    cz
    cZ
    cuz
    @23
    @31
    vk
    @22
    @18
    @13
    vm
    @22
    @18
    raleq
    raleqbi1dv
    rexima
    mp2an
    syl6bbr
    ralbidv
    @0
    @1
    @2
    @28
    @21
    wb
    #
    @0
    @1
    wa
    #
    @2
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    @79
    @80
    cX
    cxmt
    cdm
    #
    wcel
    #
    cc
    cvv
    wcel
    #
    wa
    @2
    cZ
    cc
    wss
    #
    wa
    @81
    @2
    @80
    @83
    @84
    @0
    @83
    @1
    cD
    cX
    cxmt
    elfvdm
    adantr
    cnex
    jctir
    @2
    @85
    cZ
    cz
    cc
    @78
    zsscn
    sstri
    jctr
    cX
    cc
    cZ
    cF
    @82
    cvv
    elpm2r
    syl2an
    @80
    @28
    @81
    @21
    @80
    vx
    cD
    vj
    vk
    vm
    cF
    cM
    cX
    cZ
    caucfil.1
    @0
    @1
    simpl
    @0
    @1
    simpr
    iscau3
    baibd
    syldan
    3impa
    @30
    @25
    cX
    cF
    cfm
    co
    cfv
    #
    @29
    wcel
    #
    @3
    @27
    cL
    @86
    @29
    caucfil.2
    eleq1i
    @1
    @0
    @25
    cZ
    cfbas
    cfv
    wcel
    @2
    @87
    @27
    wb
    cM
    cZ
    caucfil.1
    uzfbas
    vx
    vu
    vk
    vm
    @25
    cD
    cF
    cX
    cZ
    fmcfil
    syl3an2
    syl5bb
    3bitr4d
end
