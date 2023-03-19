include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "crp.mm"
include "cin.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "csb.mm"
include "cif.mm"
include "ccnp.mm"
include "cfv.mm"
include "wcel.mm"
include "cpnf.mm"
include "cico.mm"
include "cres.mm"
include "wss.mm"
include "inss1.mm"
include "resmpt.mm"
include "mp1i.mm"
include "cioo.mm"
include "cxr.mm"
include "clt.mm"
include "0xr.mm"
include "0lt1.mm"
include "cle.mm"
include "df-ioo.mm"
include "df-ico.mm"
include "xrltletr.mm"
include "ixxss1.mm"
include "mp2an.mm"
include "ioorp.mm"
include "sseqtri.mm"
include "sslin.mm"
include "ax-mp.mm"
include "eqtr4d.mm"
include "resres.mm"
include "3eqtr4g.mm"
include "wfn.mm"
include "cc.mm"
include "wf.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffn.mm"
include "syl.mm"
include "fnresdm.mm"
include "reseq1d.mm"
include "wrel.mm"
include "cdm.mm"
include "sseli.mm"
include "sylan2.mm"
include "frel.mm"
include "dmmptd.mm"
include "syl6eqss.mm"
include "relssres.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "breq1d.mm"
include "1red.mm"
include "rlimresb.mm"
include "cr.mm"
include "syl5ss.mm"
include "3bitr4d.mm"
include "wa.mm"
include "inss2.mm"
include "a1i.mm"
include "sselda.mm"
include "rpreccld.mm"
include "rpne0d.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "oveq2.mm"
include "wne.mm"
include "rpcnne0.mm"
include "recrec.mm"
include "3syl.mm"
include "sylan9eqr.mm"
include "eqcomd.mm"
include "csbied.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "ad2antrr.mm"
include "wn.mm"
include "w3a.mm"
include "wb.mm"
include "0re.mm"
include "pnfxr.mm"
include "elico2.mm"
include "sylib.mm"
include "simp1d.mm"
include "adantr.mm"
include "wo.mm"
include "simp2d.mm"
include "leloe.mm"
include "sylancr.mm"
include "mpbid.mm"
include "ord.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "con1d.mm"
include "imp.mm"
include "elrpd.mm"
include "csbeq1d.mm"
include "wral.mm"
include "simplr.mm"
include "simpll.mm"
include "rpreccl.mm"
include "adantl.mm"
include "ralrimiva.mm"
include "eleq1.mm"
include "eleq1d.mm"
include "bibi12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "bitr2d.mm"
include "elind.mm"
include "eqeltrd.mm"
include "eqeltrrd.mm"
include "ifclda.mm"
include "biantrud.mm"
include "bitrd.mm"
include "elin.mm"
include "syl6bbr.mm"
include "iftrue.mm"
include "eqeq1.mm"
include "csbeq1.mm"
include "ifbieq2d.mm"
include "rlimcnp.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfif.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "eleq1i.mm"
include "3bitr2d.mm"

theorem rlimcnp2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cJ: class J
  let cK: class K
  let vw: setvar w
  let vz: setvar z
  assume rlimcnp2.a: |- ( ph -> A C_ ( 0 [,) +oo ) )
  assume rlimcnp2.0: |- ( ph -> 0 e. A )
  assume rlimcnp2.b: |- ( ph -> B C_ RR )
  assume rlimcnp2.c: |- ( ph -> C e. CC )
  assume rlimcnp2.r: |- ( ( ph /\ y e. B ) -> S e. CC )
  assume rlimcnp2.d: |- ( ( ph /\ y e. RR+ ) -> ( y e. B <-> ( 1 / y ) e. A ) )
  assume rlimcnp2.s: |- ( y = ( 1 / x ) -> S = R )
  assume rlimcnp2.j: |- J = ( TopOpen ` CCfld )
  assume rlimcnp2.k: |- K = ( J |`t A )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint R y
  disjoint S x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B w
  disjoint C w
  disjoint ph w
  disjoint R w
  assert |- ( ph -> ( ( y e. B |-> S ) ~~>r C <-> ( x e. A |-> if ( x = 0 , C , R ) ) e. ( ( K CnP J ) ` 0 ) ) )

  proof
    wph
    vy
    cB
    cS
    cmpt
    #
    cC
    crli
    wbr
    #
    vy
    cB
    crp
    cin
    #
    cS
    cmpt
    #
    cC
    crli
    wbr
    #
    vy
    @2
    c1
    vy
    cv
    #
    cdiv
    co
    #
    cc0
    wceq
    #
    cC
    vx
    @6
    cR
    csb
    #
    cif
    #
    cmpt
    #
    cC
    crli
    wbr
    #
    vx
    cA
    vx
    cv
    #
    cc0
    wceq
    #
    cC
    cR
    cif
    #
    cmpt
    #
    cc0
    cK
    cJ
    ccnp
    co
    cfv
    #
    wcel
    #
    wph
    @0
    c1
    cpnf
    cico
    co
    #
    cres
    #
    cC
    crli
    wbr
    @3
    @18
    cres
    #
    cC
    crli
    wbr
    @1
    @4
    wph
    @19
    @20
    cC
    crli
    wph
    @0
    cB
    cres
    #
    @18
    cres
    #
    @3
    cB
    cres
    #
    @18
    cres
    #
    @19
    @20
    wph
    @0
    cB
    @18
    cin
    #
    cres
    #
    @3
    @25
    cres
    #
    @22
    @24
    wph
    @26
    vy
    @25
    cS
    cmpt
    #
    @27
    @25
    cB
    wss
    @26
    @28
    wceq
    wph
    cB
    @18
    inss1
    vy
    cB
    @25
    cS
    resmpt
    mp1i
    @25
    @2
    wss
    #
    @27
    @28
    wceq
    wph
    @18
    crp
    wss
    @29
    @18
    cc0
    cpnf
    cioo
    co
    #
    crp
    cc0
    cxr
    wcel
    cc0
    c1
    clt
    wbr
    @18
    @30
    wss
    0xr
    0lt1
    vx
    vy
    vz
    vw
    cc0
    c1
    cpnf
    cico
    clt
    clt
    cle
    cioo
    clt
    vx
    vy
    vz
    df-ioo
    vx
    vy
    vz
    df-ico
    cc0
    c1
    vw
    cv
    #
    xrltletr
    ixxss1
    mp2an
    ioorp
    sseqtri
    @18
    crp
    cB
    sslin
    ax-mp
    vy
    @2
    @25
    cS
    resmpt
    mp1i
    eqtr4d
    @0
    cB
    @18
    resres
    @3
    cB
    @18
    resres
    3eqtr4g
    wph
    @21
    @0
    @18
    wph
    @0
    cB
    wfn
    #
    @21
    @0
    wceq
    wph
    cB
    cc
    @0
    wf
    @32
    wph
    vy
    cB
    cS
    cc
    @0
    rlimcnp2.r
    @0
    eqid
    fmptd
    #
    cB
    cc
    @0
    ffn
    syl
    cB
    @0
    fnresdm
    syl
    reseq1d
    wph
    @23
    @3
    @18
    wph
    @3
    wrel
    #
    @3
    cdm
    #
    cB
    wss
    @23
    @3
    wceq
    wph
    @2
    cc
    @3
    wf
    @34
    wph
    vy
    @2
    cS
    cc
    @3
    @5
    @2
    wcel
    #
    wph
    @5
    cB
    wcel
    #
    cS
    cc
    wcel
    @2
    cB
    @5
    cB
    crp
    inss1
    #
    sseli
    rlimcnp2.r
    sylan2
    #
    @3
    eqid
    #
    fmptd
    #
    @2
    cc
    @3
    frel
    syl
    wph
    @35
    @2
    cB
    wph
    vy
    @3
    @2
    cS
    cc
    @40
    @39
    dmmptd
    @38
    syl6eqss
    @3
    cB
    relssres
    syl2anc
    reseq1d
    3eqtr3d
    breq1d
    wph
    cB
    c1
    cC
    @0
    @33
    rlimcnp2.b
    wph
    1red
    #
    rlimresb
    wph
    @2
    c1
    cC
    @3
    @41
    wph
    @2
    cB
    cr
    @38
    rlimcnp2.b
    syl5ss
    @42
    rlimresb
    3bitr4d
    wph
    @10
    @3
    cC
    crli
    wph
    vy
    @2
    @9
    cS
    wph
    @36
    wa
    #
    @9
    @8
    cS
    @43
    @7
    cC
    @8
    @43
    @6
    cc0
    @43
    @6
    @43
    @5
    wph
    @2
    crp
    @5
    @2
    crp
    wss
    wph
    cB
    crp
    inss2
    a1i
    #
    sselda
    #
    rpreccld
    #
    rpne0d
    neneqd
    iffalsed
    @43
    vx
    @6
    cR
    cS
    crp
    @46
    @43
    @12
    @6
    wceq
    #
    wa
    #
    cS
    cR
    @48
    @5
    c1
    @12
    cdiv
    co
    #
    wceq
    cS
    cR
    wceq
    @48
    @49
    @5
    @47
    @43
    @49
    c1
    @6
    cdiv
    co
    #
    @5
    @12
    @6
    c1
    cdiv
    oveq2
    @43
    @5
    crp
    wcel
    @5
    cc
    wcel
    @5
    cc0
    wne
    wa
    @50
    @5
    wceq
    @45
    @5
    rpcnne0
    @5
    recrec
    3syl
    sylan9eqr
    eqcomd
    rlimcnp2.s
    syl
    eqcomd
    csbied
    #
    eqtrd
    mpteq2dva
    breq1d
    wph
    @11
    vw
    cA
    @31
    cc0
    wceq
    #
    cC
    vx
    @31
    cR
    csb
    #
    cif
    #
    cmpt
    #
    @16
    wcel
    @17
    wph
    vw
    vy
    cA
    @2
    cC
    @54
    @9
    cJ
    cK
    rlimcnp2.a
    rlimcnp2.0
    @44
    wph
    @31
    cA
    wcel
    #
    wa
    #
    @52
    cC
    @53
    cc
    wph
    cC
    cc
    wcel
    @56
    @52
    rlimcnp2.c
    ad2antrr
    @57
    @52
    wn
    #
    wa
    #
    vx
    c1
    c1
    @31
    cdiv
    co
    #
    cdiv
    co
    #
    cR
    csb
    #
    @53
    cc
    @59
    vx
    @61
    @31
    cR
    @59
    @31
    crp
    wcel
    #
    @61
    @31
    wceq
    #
    @59
    @31
    @57
    @31
    cr
    wcel
    #
    @58
    @57
    @65
    cc0
    @31
    cle
    wbr
    #
    @31
    cpnf
    clt
    wbr
    #
    @57
    @31
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @65
    @66
    @67
    w3a
    #
    wph
    cA
    @68
    @31
    rlimcnp2.a
    sselda
    cc0
    cr
    wcel
    #
    cpnf
    cxr
    wcel
    @69
    @70
    wb
    0re
    pnfxr
    cc0
    cpnf
    @31
    elico2
    mp2an
    sylib
    #
    simp1d
    #
    adantr
    @57
    @58
    cc0
    @31
    clt
    wbr
    #
    @57
    @74
    @52
    @57
    @74
    wn
    cc0
    @31
    wceq
    #
    @52
    @57
    @74
    @75
    @57
    @66
    @74
    @75
    wo
    #
    @57
    @65
    @66
    @67
    @72
    simp2d
    @57
    @71
    @65
    @66
    @76
    wb
    0re
    @73
    cc0
    @31
    leloe
    sylancr
    mpbid
    ord
    cc0
    @31
    eqcom
    syl6ib
    con1d
    imp
    elrpd
    #
    @63
    @31
    cc
    wcel
    @31
    cc0
    wne
    wa
    @64
    @31
    rpcnne0
    @31
    recrec
    syl
    #
    syl
    csbeq1d
    @59
    @60
    @2
    wcel
    #
    @8
    cc
    wcel
    #
    vy
    @2
    wral
    #
    @62
    cc
    wcel
    #
    @59
    cB
    crp
    @60
    @59
    @56
    @60
    cB
    wcel
    #
    wph
    @56
    @58
    simplr
    @59
    wph
    @63
    @56
    @83
    wb
    wph
    @56
    @58
    simpll
    @77
    wph
    @63
    wa
    #
    @83
    @61
    cA
    wcel
    #
    @56
    @84
    @60
    crp
    wcel
    #
    @37
    @6
    cA
    wcel
    #
    wb
    #
    vy
    crp
    wral
    #
    @83
    @85
    wb
    #
    @63
    @86
    wph
    @31
    rpreccl
    adantl
    #
    wph
    @89
    @63
    wph
    @88
    vy
    crp
    rlimcnp2.d
    ralrimiva
    adantr
    @88
    @90
    vy
    @60
    crp
    @5
    @60
    wceq
    #
    @37
    @83
    @87
    @85
    @5
    @60
    cB
    eleq1
    @92
    @6
    @61
    cA
    @5
    @60
    c1
    cdiv
    oveq2
    #
    eleq1d
    bibi12d
    rspcv
    sylc
    @84
    @61
    @31
    cA
    @63
    @64
    wph
    @78
    adantl
    eleq1d
    bitr2d
    #
    syl2anc
    mpbid
    @59
    @31
    @77
    rpreccld
    elind
    wph
    @81
    @56
    @58
    wph
    @80
    vy
    @2
    @43
    @8
    cS
    cc
    @51
    @39
    eqeltrd
    ralrimiva
    ad2antrr
    @80
    @82
    vy
    @60
    @2
    @92
    @8
    @62
    cc
    @92
    vx
    @6
    @61
    cR
    @93
    csbeq1d
    eleq1d
    rspcv
    sylc
    eqeltrrd
    ifclda
    @84
    @56
    @83
    @86
    wa
    #
    @79
    @84
    @56
    @83
    @95
    @94
    @84
    @86
    @83
    @91
    biantrud
    bitrd
    @60
    cB
    crp
    elin
    syl6bbr
    @52
    cC
    @53
    iftrue
    @31
    @6
    wceq
    @52
    @7
    @53
    @8
    cC
    @31
    @6
    cc0
    eqeq1
    vx
    @31
    @6
    cR
    csbeq1
    ifbieq2d
    rlimcnp2.j
    rlimcnp2.k
    rlimcnp
    @15
    @55
    @16
    vx
    vw
    cA
    @14
    @54
    vw
    @14
    nfcv
    @52
    vx
    cC
    @53
    @52
    vx
    nfv
    vx
    cC
    nfcv
    vx
    @31
    cR
    nfcsb1v
    nfif
    @12
    @31
    wceq
    @13
    @52
    cR
    @53
    cC
    @12
    @31
    cc0
    eqeq1
    vx
    @31
    cR
    csbeq1a
    ifbieq2d
    cbvmpt
    eleq1i
    syl6bbr
    3bitr2d
end
