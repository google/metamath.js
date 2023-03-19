include "cprime.mm"
include "wcel.mm"
include "cid.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cres.mm"
include "cgsu.mm"
include "cneg.mm"
include "cfa.mm"
include "cfv.mm"
include "caddc.mm"
include "cdvds.mm"
include "cmo.mm"
include "wceq.mm"
include "wbr.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "wral.mm"
include "cuz.mm"
include "cn.mm"
include "prmuz2.mm"
include "uz2m1nn.mm"
include "syl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "wa.mm"
include "cmul.mm"
include "cz.mm"
include "wn.mm"
include "simpl.mm"
include "elfzelz.mm"
include "adantl.mm"
include "prmnn.mm"
include "fzm1ndvds.mm"
include "sylan.mm"
include "eqid.mm"
include "prmdiv.mm"
include "syl3anc.mm"
include "simpld.mm"
include "ralrimiva.mm"
include "cpw.mm"
include "ovex.mm"
include "pwid.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "mpbiran.mm"
include "sylanbrc.mm"
include "cfn.mm"
include "wi.mm"
include "fzfi.mm"
include "eleq1.mm"
include "reseq2.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wpss.mm"
include "wal.mm"
include "bi2.04.mm"
include "pm2.27.mm"
include "com34.mm"
include "syl5bi.mm"
include "alimdv.mm"
include "df-ral.mm"
include "syl6ibr.mm"
include "w3a.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "wilthlem2.mm"
include "3exp.mm"
include "syldc.mm"
include "a1i.mm"
include "findcard3.mm"
include "ax-mp.mm"
include "mpd.mm"
include "wb.mm"
include "ccnfld.mm"
include "cnfld1.mm"
include "ringidval.mm"
include "ccrg.mm"
include "ccmn.mm"
include "cncrng.mm"
include "crngmgp.mm"
include "mp1i.mm"
include "csubrg.mm"
include "csubmnd.mm"
include "zsubrg.mm"
include "subrgsubm.mm"
include "wf.mm"
include "wss.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "ssriv.mm"
include "fss.mm"
include "mp2an.mm"
include "cvv.mm"
include "1ex.mm"
include "fdmfifsupp.mm"
include "gsumsubmcl.mm"
include "1z.mm"
include "znegcl.mm"
include "moddvds.mm"
include "mpbid.mm"
include "ccom.mm"
include "cseq.mm"
include "fcoi1.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5eq.mm"
include "seqfveq.mm"
include "cc.mm"
include "csupp.mm"
include "ccntz.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "crg.mm"
include "cmnd.mm"
include "cnring.mm"
include "ringmgp.mm"
include "zsscn.mm"
include "cntzcmnf.mm"
include "wf1.mm"
include "f1of1.mm"
include "crn.mm"
include "cdm.mm"
include "suppssdm.mm"
include "dmresi.mm"
include "sseqtri.mm"
include "rnresi.mm"
include "sseqtr4i.mm"
include "gsumval3.mm"
include "facnn.mm"
include "3eqtr4d.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "faccl.mm"
include "nncnd.mm"
include "ax-1cn.mm"
include "subneg.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "breqtrd.mm"

theorem wilthlem3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cT: class T
  let vs: setvar s
  let vt: setvar t
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let wph: wff ph
  let cS: class S
  assume wilthlem.t: |- T = ( mulGrp ` CCfld )
  assume wilthlem.a: |- A = { x e. ~P ( 1 ... ( P - 1 ) ) | ( ( P - 1 ) e. x /\ A. y e. x ( ( y ^ ( P - 2 ) ) mod P ) e. x ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint P x
  disjoint P y
  disjoint T x
  disjoint T y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint k s
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint P k
  disjoint s w
  disjoint s z
  disjoint P s
  disjoint t w
  disjoint t z
  disjoint P t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint P w
  disjoint x z
  disjoint y z
  disjoint P z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S s
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint T z
  assert |- ( P e. Prime -> P || ( ( ! ` ( P - 1 ) ) + 1 ) )

  proof
    cP
    cprime
    wcel
    #
    cP
    cT
    cid
    c1
    cP
    c1
    cmin
    co
    #
    cfz
    co
    #
    cres
    #
    cgsu
    co
    #
    c1
    cneg
    #
    cmin
    co
    #
    @1
    cfa
    cfv
    #
    c1
    caddc
    co
    #
    cdvds
    @0
    @4
    cP
    cmo
    co
    #
    @5
    cP
    cmo
    co
    #
    wceq
    #
    cP
    @6
    cdvds
    wbr
    #
    @0
    @2
    cA
    wcel
    #
    @11
    @0
    @1
    @2
    wcel
    #
    vy
    cv
    #
    cP
    c2
    cmin
    co
    cexp
    co
    cP
    cmo
    co
    #
    @2
    wcel
    #
    vy
    @2
    wral
    #
    @13
    @0
    @1
    c1
    cuz
    cfv
    #
    wcel
    @14
    @0
    @1
    cn
    @19
    @0
    cP
    c2
    cuz
    cfv
    wcel
    @1
    cn
    wcel
    #
    cP
    prmuz2
    cP
    uz2m1nn
    syl
    #
    nnuz
    syl6eleq
    #
    c1
    @1
    eluzfz2
    syl
    @0
    @17
    vy
    @2
    @0
    @15
    @2
    wcel
    #
    wa
    #
    @17
    cP
    @15
    @16
    cmul
    co
    c1
    cmin
    co
    cdvds
    wbr
    #
    @24
    @0
    @15
    cz
    wcel
    #
    cP
    @15
    cdvds
    wbr
    wn
    #
    @17
    @25
    wa
    @0
    @23
    simpl
    @23
    @26
    @0
    @15
    c1
    @1
    elfzelz
    #
    adantl
    @0
    cP
    cn
    wcel
    #
    @23
    @27
    cP
    prmnn
    #
    cP
    @15
    fzm1ndvds
    sylan
    @15
    cP
    @16
    @16
    eqid
    prmdiv
    syl3anc
    simpld
    ralrimiva
    @13
    @2
    @2
    cpw
    #
    wcel
    @14
    @18
    wa
    #
    @2
    c1
    @1
    cfz
    ovex
    pwid
    @1
    vx
    cv
    #
    wcel
    #
    @16
    @33
    wcel
    #
    vy
    @33
    wral
    #
    wa
    @32
    vx
    @2
    @31
    cA
    @33
    @2
    wceq
    @34
    @14
    @36
    @18
    @33
    @2
    @1
    eleq2
    @35
    @17
    vy
    @33
    @2
    @33
    @2
    @16
    eleq2
    raleqbi1dv
    anbi12d
    wilthlem.a
    elrab2
    mpbiran
    sylanbrc
    @2
    cfn
    wcel
    #
    @0
    @13
    @11
    wi
    #
    wi
    #
    c1
    @1
    fzfi
    #
    @0
    vs
    cv
    #
    cA
    wcel
    #
    cT
    cid
    @41
    cres
    #
    cgsu
    co
    #
    cP
    cmo
    co
    #
    @10
    wceq
    #
    wi
    #
    wi
    #
    @0
    vt
    cv
    #
    cA
    wcel
    #
    cT
    cid
    @49
    cres
    #
    cgsu
    co
    #
    cP
    cmo
    co
    #
    @10
    wceq
    #
    wi
    #
    wi
    #
    @39
    vs
    vt
    @2
    @41
    @49
    wceq
    #
    @47
    @55
    @0
    @57
    @42
    @50
    @46
    @54
    @41
    @49
    cA
    eleq1
    @57
    @45
    @53
    @10
    @57
    @44
    @52
    cP
    cmo
    @57
    @43
    @51
    cT
    cgsu
    @41
    @49
    cid
    reseq2
    oveq2d
    oveq1d
    eqeq1d
    imbi12d
    imbi2d
    @41
    @2
    wceq
    #
    @47
    @38
    @0
    @58
    @42
    @13
    @46
    @11
    @41
    @2
    cA
    eleq1
    @58
    @45
    @9
    @10
    @58
    @44
    @4
    cP
    cmo
    @58
    @43
    @3
    cT
    cgsu
    @41
    @2
    cid
    reseq2
    oveq2d
    oveq1d
    eqeq1d
    imbi12d
    imbi2d
    @41
    @49
    wpss
    #
    @48
    wi
    #
    vs
    wal
    #
    @56
    wi
    @49
    cfn
    wcel
    @0
    @61
    @59
    @46
    wi
    #
    vs
    cA
    wral
    #
    @55
    @0
    @61
    @42
    @62
    wi
    #
    vs
    wal
    @63
    @0
    @60
    @64
    vs
    @60
    @0
    @59
    @47
    wi
    #
    wi
    #
    @0
    @64
    @59
    @0
    @47
    bi2.04
    @0
    @66
    @59
    @42
    @46
    @0
    @65
    pm2.27
    com34
    syl5bi
    alimdv
    @62
    vs
    cA
    df-ral
    syl6ibr
    @0
    @63
    @50
    @54
    @0
    @63
    @50
    w3a
    vx
    vy
    cA
    cP
    @49
    cT
    vs
    wilthlem.t
    wilthlem.a
    @0
    @63
    @50
    simp1
    @0
    @63
    @50
    simp3
    @0
    @63
    @50
    simp2
    wilthlem2
    3exp
    syldc
    a1i
    findcard3
    ax-mp
    mpd
    @0
    @29
    @4
    cz
    wcel
    @5
    cz
    wcel
    #
    @11
    @12
    wb
    @30
    @0
    @2
    cz
    @3
    cT
    cfn
    c1
    ccnfld
    c1
    cT
    wilthlem.t
    cnfld1
    ringidval
    #
    ccnfld
    ccrg
    wcel
    cT
    ccmn
    wcel
    @0
    cncrng
    ccnfld
    cT
    wilthlem.t
    crngmgp
    mp1i
    #
    @37
    @0
    @40
    a1i
    #
    cz
    ccnfld
    csubrg
    cfv
    wcel
    cz
    cT
    csubmnd
    cfv
    wcel
    @0
    zsubrg
    cz
    ccnfld
    cT
    wilthlem.t
    subrgsubm
    mp1i
    @2
    cz
    @3
    wf
    #
    @0
    @2
    @2
    @3
    wf
    #
    @2
    cz
    wss
    @71
    @2
    @2
    @3
    wf1o
    #
    @72
    @2
    f1oi
    #
    @2
    @2
    @3
    f1of
    ax-mp
    #
    vy
    @2
    cz
    @28
    ssriv
    @2
    @2
    cz
    @3
    fss
    mp2an
    #
    a1i
    #
    @0
    @2
    cz
    @3
    cvv
    c1
    @77
    @70
    c1
    cvv
    wcel
    @0
    1ex
    a1i
    fdmfifsupp
    gsumsubmcl
    c1
    cz
    wcel
    @67
    @0
    1z
    c1
    znegcl
    mp1i
    @4
    @5
    cP
    moddvds
    syl3anc
    mpbid
    @0
    @6
    @7
    @5
    cmin
    co
    #
    @8
    @0
    @4
    @7
    @5
    cmin
    @0
    @1
    cmul
    @3
    @3
    ccom
    #
    c1
    cseq
    cfv
    @1
    cmul
    cid
    c1
    cseq
    cfv
    #
    @4
    @7
    @0
    cmul
    vk
    @79
    cid
    c1
    @1
    @22
    vk
    cv
    #
    @2
    wcel
    #
    @81
    @79
    cfv
    #
    @81
    cid
    cfv
    #
    wceq
    @0
    @82
    @83
    @81
    @3
    cfv
    @84
    @81
    @79
    @3
    @72
    @79
    @3
    wceq
    @75
    @2
    @2
    @3
    fcoi1
    ax-mp
    fveq1i
    @81
    @2
    cid
    fvres
    syl5eq
    adantl
    seqfveq
    @0
    @2
    cc
    cmul
    @3
    cT
    @3
    @1
    cfn
    @79
    c1
    csupp
    co
    #
    c1
    cT
    ccntz
    cfv
    #
    cc
    ccnfld
    cT
    wilthlem.t
    cnfldbas
    mgpbas
    #
    @68
    ccnfld
    cmul
    cT
    wilthlem.t
    cnfldmul
    mgpplusg
    @86
    eqid
    #
    ccnfld
    crg
    wcel
    cT
    cmnd
    wcel
    @0
    cnring
    ccnfld
    cT
    wilthlem.t
    ringmgp
    mp1i
    @70
    @2
    cc
    @3
    wf
    #
    @0
    @71
    cz
    cc
    wss
    @89
    @76
    zsscn
    @2
    cz
    cc
    @3
    fss
    mp2an
    a1i
    #
    @0
    @2
    cc
    @3
    cT
    @86
    @87
    @88
    @69
    @90
    cntzcmnf
    @21
    @73
    @2
    @2
    @3
    wf1
    @0
    @74
    @2
    @2
    @3
    f1of1
    mp1i
    @3
    c1
    csupp
    co
    #
    @3
    crn
    #
    wss
    @0
    @91
    @2
    @92
    @91
    @3
    cdm
    @2
    @3
    c1
    suppssdm
    @2
    dmresi
    sseqtri
    @2
    rnresi
    sseqtr4i
    a1i
    @85
    eqid
    gsumval3
    @0
    @20
    @7
    @80
    wceq
    @21
    @1
    facnn
    syl
    3eqtr4d
    oveq1d
    @0
    @7
    cc
    wcel
    c1
    cc
    wcel
    @78
    @8
    wceq
    @0
    @7
    @0
    @1
    cn0
    wcel
    #
    @7
    cn
    wcel
    @0
    @29
    @93
    @30
    cP
    nnm1nn0
    syl
    @1
    faccl
    syl
    nncnd
    ax-1cn
    @7
    c1
    subneg
    sylancl
    eqtrd
    breqtrd
end
