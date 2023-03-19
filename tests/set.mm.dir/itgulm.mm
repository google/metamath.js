include "cv.mm"
include "cfv.mm"
include "citg.mm"
include "cmpt.mm"
include "cli.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cvol.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "cz.mm"
include "adantr.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "wfn.mm"
include "culm.mm"
include "cibl.mm"
include "ffn.mm"
include "syl.mm"
include "ulmf2.mm"
include "syl2anc.mm"
include "eqidd.mm"
include "simpr.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "covol.mm"
include "cdm.mm"
include "wss.mm"
include "wceq.mm"
include "ulmcl.mm"
include "fdm.mm"
include "3syl.mm"
include "cmbf.mm"
include "iblulm.mm"
include "iblmbf.mm"
include "mbfdm.mm"
include "eqeltrrd.mm"
include "mblss.mm"
include "ovolge0.mm"
include "mblvol.mm"
include "breqtrrd.mm"
include "ge0p1rpd.mm"
include "rpdivcld.mm"
include "ulmi.mm"
include "wi.mm"
include "uztrn2.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "adantllr.mm"
include "adantlrr.mm"
include "feqmptd.mm"
include "ad2ant2r.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "itgsub.mm"
include "fveq2d.mm"
include "subcld.mm"
include "iblsub.mm"
include "itgcl.mm"
include "abscld.mm"
include "iblabs.mm"
include "itgrecl.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "itgabs.mm"
include "cmul.mm"
include "rpred.mm"
include "remulcld.mm"
include "csn.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "rpcnd.mm"
include "iblconst.mm"
include "syl3anc.mm"
include "syl5eqelr.mm"
include "simprr.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "ltled.mm"
include "itgle.mm"
include "itgconst.mm"
include "breqtrd.mm"
include "recnd.mm"
include "rpne0d.mm"
include "div23d.mm"
include "ltp1d.mm"
include "wb.mm"
include "peano2re.mm"
include "rpgt0.mm"
include "ltmul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ltdivmul2d.mm"
include "mpbird.mm"
include "eqbrtrrd.mm"
include "lelttrd.mm"
include "expr.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "fveq1d.mm"
include "itgeq2dv.mm"
include "eqid.mm"
include "itgex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "clim2c.mm"

theorem itgulm
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vn: setvar n
  let vr: setvar r
  let vz: setvar z
  assume itgulm.z: |- Z = ( ZZ>= ` M )
  assume itgulm.m: |- ( ph -> M e. ZZ )
  assume itgulm.f: |- ( ph -> F : Z --> L^1 )
  assume itgulm.u: |- ( ph -> F ( ~~>u ` S ) G )
  assume itgulm.s: |- ( ph -> ( vol ` S ) e. RR )

  disjoint k x
  disjoint F k
  disjoint F x
  disjoint G k
  disjoint G x
  disjoint k ph
  disjoint ph x
  disjoint M k
  disjoint M x
  disjoint S k
  disjoint S x
  disjoint Z k
  disjoint Z x
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint k n
  disjoint k r
  disjoint k z
  disjoint n r
  disjoint n x
  disjoint n z
  disjoint F n
  disjoint r x
  disjoint r z
  disjoint F r
  disjoint x z
  disjoint F z
  disjoint G j
  disjoint G n
  disjoint G r
  disjoint G z
  disjoint j ph
  disjoint n ph
  disjoint ph r
  disjoint ph z
  disjoint M j
  disjoint M n
  disjoint M z
  disjoint S j
  disjoint S n
  disjoint S r
  disjoint S z
  disjoint Z j
  disjoint Z n
  disjoint Z r
  disjoint Z z
  assert |- ( ph -> ( k e. Z |-> S. S ( ( F ` k ) ` x ) _d x ) ~~> S. S ( G ` x ) _d x )

  proof
    wph
    vk
    cZ
    vx
    cS
    vx
    cv
    #
    vk
    cv
    #
    cF
    cfv
    #
    cfv
    #
    citg
    #
    cmpt
    #
    vx
    cS
    @0
    cG
    cfv
    #
    citg
    #
    cli
    wbr
    vx
    cS
    @0
    vn
    cv
    #
    cF
    cfv
    #
    cfv
    #
    citg
    #
    @7
    cmin
    co
    #
    cabs
    cfv
    #
    vr
    cv
    #
    clt
    wbr
    #
    vn
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
    vr
    crp
    wral
    wph
    @19
    vr
    crp
    wph
    @14
    crp
    wcel
    #
    wa
    #
    vz
    cv
    #
    @9
    cfv
    #
    @22
    cG
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @14
    cS
    cvol
    cfv
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vn
    @17
    wral
    #
    vj
    cZ
    wrex
    @19
    @21
    vz
    @24
    @23
    @29
    cS
    vj
    vn
    cF
    cG
    cM
    cZ
    itgulm.z
    wph
    cM
    cz
    wcel
    @20
    itgulm.m
    adantr
    wph
    cZ
    cc
    cS
    cmap
    co
    #
    cF
    wf
    #
    @20
    wph
    cF
    cZ
    wfn
    #
    cF
    cG
    cS
    culm
    cfv
    wbr
    #
    @34
    wph
    cZ
    cibl
    cF
    wf
    @35
    itgulm.f
    cZ
    cibl
    cF
    ffn
    syl
    itgulm.u
    cS
    cF
    cG
    cZ
    ulmf2
    syl2anc
    #
    adantr
    @21
    @8
    cZ
    wcel
    #
    @22
    cS
    wcel
    #
    wa
    wa
    @23
    eqidd
    @21
    @39
    wa
    @24
    eqidd
    wph
    @36
    @20
    itgulm.u
    adantr
    @21
    @14
    @28
    wph
    @20
    simpr
    @21
    @27
    wph
    @27
    cr
    wcel
    #
    @20
    itgulm.s
    adantr
    wph
    cc0
    @27
    cle
    wbr
    @20
    wph
    cc0
    cS
    covol
    cfv
    #
    @27
    cle
    wph
    cS
    cvol
    cdm
    #
    wcel
    #
    cS
    cr
    wss
    cc0
    @41
    cle
    wbr
    wph
    cG
    cdm
    #
    cS
    @42
    wph
    @36
    cS
    cc
    cG
    wf
    #
    @44
    cS
    wceq
    itgulm.u
    cS
    cF
    cG
    ulmcl
    #
    cS
    cc
    cG
    fdm
    3syl
    wph
    cG
    cibl
    wcel
    cG
    cmbf
    wcel
    @44
    @42
    wcel
    wph
    cS
    cF
    cG
    cM
    cZ
    itgulm.z
    itgulm.m
    itgulm.f
    itgulm.u
    itgulm.s
    iblulm
    #
    cG
    iblmbf
    cG
    mbfdm
    3syl
    eqeltrrd
    #
    cS
    mblss
    cS
    ovolge0
    3syl
    wph
    @43
    @27
    @41
    wceq
    @48
    cS
    mblvol
    syl
    breqtrrd
    adantr
    ge0p1rpd
    #
    rpdivcld
    #
    ulmi
    @21
    @32
    @18
    vj
    cZ
    @21
    @16
    cZ
    wcel
    #
    wa
    @31
    @15
    vn
    @17
    @21
    @51
    @8
    @17
    wcel
    #
    @31
    @15
    wi
    #
    @51
    @52
    wa
    @21
    @38
    @53
    cM
    @8
    @16
    cZ
    itgulm.z
    uztrn2
    @21
    @38
    @31
    @15
    @21
    @38
    @31
    wa
    #
    wa
    #
    vx
    cS
    @10
    @6
    cmin
    co
    #
    citg
    #
    cabs
    cfv
    #
    @13
    @14
    clt
    @55
    @57
    @12
    cabs
    @55
    vx
    cS
    @10
    @6
    cc
    @21
    @38
    @0
    cS
    wcel
    #
    @10
    cc
    wcel
    #
    @31
    wph
    @38
    @59
    @60
    @20
    wph
    @38
    wa
    #
    cS
    cc
    @0
    @9
    @61
    @9
    @33
    wcel
    cS
    cc
    @9
    wf
    wph
    cZ
    @33
    @8
    cF
    @37
    ffvelrnda
    @9
    cc
    cS
    elmapi
    syl
    #
    ffvelrnda
    #
    adantllr
    adantlrr
    #
    wph
    @38
    vx
    cS
    @10
    cmpt
    #
    cibl
    wcel
    @20
    @31
    @61
    @9
    @65
    cibl
    @61
    vx
    cS
    cc
    @9
    @62
    feqmptd
    wph
    cZ
    cibl
    @8
    cF
    itgulm.f
    ffvelrnda
    eqeltrrd
    #
    ad2ant2r
    #
    @21
    @59
    @6
    cc
    wcel
    #
    @54
    wph
    @59
    @68
    @20
    wph
    cS
    cc
    @0
    cG
    wph
    @36
    @45
    itgulm.u
    @46
    syl
    #
    ffvelrnda
    #
    adantlr
    adantlr
    #
    wph
    vx
    cS
    @6
    cmpt
    #
    cibl
    wcel
    @20
    @54
    wph
    cG
    @72
    cibl
    wph
    vx
    cS
    cc
    cG
    @69
    feqmptd
    @47
    eqeltrrd
    #
    ad2antrr
    #
    itgsub
    fveq2d
    @55
    @58
    vx
    cS
    @56
    cabs
    cfv
    #
    citg
    #
    @14
    @55
    @57
    @55
    vx
    cS
    @56
    cc
    @55
    @59
    wa
    #
    @10
    @6
    @64
    @71
    subcld
    #
    @55
    vx
    cS
    @10
    @6
    cc
    @64
    @67
    @71
    @74
    iblsub
    #
    itgcl
    abscld
    @55
    vx
    cS
    @75
    @77
    @56
    @78
    abscld
    #
    @55
    vx
    cS
    @56
    cc
    @78
    @79
    iblabs
    #
    itgrecl
    #
    @20
    @14
    cr
    wcel
    #
    wph
    @54
    @14
    rpre
    ad2antlr
    #
    @55
    vx
    cS
    @56
    cc
    @78
    @79
    itgabs
    @55
    @76
    @29
    @27
    cmul
    co
    #
    @14
    @82
    @55
    @29
    @27
    @55
    @29
    @21
    @29
    crp
    wcel
    @54
    @50
    adantr
    #
    rpred
    #
    wph
    @40
    @20
    @54
    itgulm.s
    ad2antrr
    #
    remulcld
    @84
    @55
    @76
    vx
    cS
    @29
    citg
    #
    @85
    cle
    @55
    vx
    cS
    @75
    @29
    @81
    @55
    vx
    cS
    @29
    cmpt
    cS
    @29
    csn
    cxp
    #
    cibl
    vx
    cS
    @29
    fconstmpt
    @55
    @43
    @40
    @29
    cc
    wcel
    #
    @90
    cibl
    wcel
    wph
    @43
    @20
    @54
    @48
    ad2antrr
    #
    @88
    @55
    @29
    @86
    rpcnd
    #
    cS
    @29
    iblconst
    syl3anc
    syl5eqelr
    @80
    @55
    @29
    cr
    wcel
    @59
    @87
    adantr
    #
    @77
    @75
    @29
    @80
    @94
    @55
    @31
    @59
    @75
    @29
    clt
    wbr
    #
    @21
    @38
    @31
    simprr
    @30
    @95
    vz
    @0
    cS
    vz
    vx
    weq
    #
    @26
    @75
    @29
    clt
    @96
    @25
    @56
    cabs
    @96
    @23
    @10
    @24
    @6
    cmin
    @22
    @0
    @9
    fveq2
    @22
    @0
    cG
    fveq2
    oveq12d
    fveq2d
    breq1d
    rspccva
    sylan
    ltled
    itgle
    @55
    @43
    @40
    @91
    @89
    @85
    wceq
    @92
    @88
    @93
    vx
    cS
    @29
    itgconst
    syl3anc
    breqtrd
    @55
    @14
    @27
    cmul
    co
    #
    @28
    cdiv
    co
    #
    @85
    @14
    clt
    @55
    @14
    @27
    @28
    @55
    @14
    @84
    recnd
    @55
    @27
    @88
    recnd
    @55
    @28
    @21
    @28
    crp
    wcel
    @54
    @49
    adantr
    #
    rpcnd
    @55
    @28
    @99
    rpne0d
    div23d
    @55
    @98
    @14
    clt
    wbr
    @97
    @14
    @28
    cmul
    co
    clt
    wbr
    #
    @55
    @27
    @28
    clt
    wbr
    #
    @100
    @55
    @27
    @88
    ltp1d
    @55
    @40
    @28
    cr
    wcel
    #
    @83
    cc0
    @14
    clt
    wbr
    #
    @101
    @100
    wb
    @88
    @55
    @40
    @102
    @88
    @27
    peano2re
    syl
    @84
    @20
    @103
    wph
    @54
    @14
    rpgt0
    ad2antlr
    @27
    @28
    @14
    ltmul2
    syl112anc
    mpbid
    @55
    @97
    @14
    @28
    @55
    @14
    @27
    @84
    @88
    remulcld
    @84
    @99
    ltdivmul2d
    mpbird
    eqbrtrrd
    lelttrd
    lelttrd
    eqbrtrrd
    expr
    sylan2
    anassrs
    ralimdva
    reximdva
    mpd
    ralrimiva
    wph
    vr
    @7
    @11
    vj
    vn
    @5
    cM
    cvv
    cZ
    itgulm.z
    itgulm.m
    @5
    cvv
    wcel
    wph
    vk
    cZ
    @4
    cZ
    cM
    cuz
    cfv
    cvv
    itgulm.z
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    @38
    @8
    @5
    cfv
    @11
    wceq
    wph
    vk
    @8
    @4
    @11
    cZ
    @5
    vk
    vn
    weq
    #
    vx
    cS
    @3
    @10
    @104
    @3
    @10
    wceq
    @59
    @104
    @0
    @2
    @9
    @1
    @8
    cF
    fveq2
    fveq1d
    adantr
    itgeq2dv
    @5
    eqid
    vx
    cS
    @10
    itgex
    fvmpt
    adantl
    wph
    vx
    cS
    @6
    cc
    @70
    @73
    itgcl
    @61
    vx
    cS
    @10
    cc
    @63
    @66
    itgcl
    clim2c
    mpbird
end
