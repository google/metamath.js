include "cmin.mm"
include "co.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cicc.mm"
include "covol.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "caddc.mm"
include "cabs.mm"
include "c1.mm"
include "cseq.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "cn.mm"
include "cmap.mm"
include "wrex.mm"
include "elovolm.mm"
include "wi.mm"
include "cpw.mm"
include "cfn.mm"
include "ctg.mm"
include "wf.mm"
include "wfn.mm"
include "ioof.mm"
include "ffn.mm"
include "ax-mp.mm"
include "dffn3.mm"
include "mpbi.mm"
include "simpr.mm"
include "reex.mm"
include "xpex.mm"
include "inex2.mm"
include "nnex.mm"
include "elmap.mm"
include "sylib.mm"
include "inss2.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fss.mm"
include "sylancl.mm"
include "fco.mm"
include "sylancr.mm"
include "adantrr.mm"
include "frn.mm"
include "syl.mm"
include "ctb.mm"
include "retopbas.mm"
include "bastg.mm"
include "syl6ss.mm"
include "fvex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "crest.mm"
include "ccmp.mm"
include "eqid.mm"
include "icccmp.mm"
include "syl2anc.mm"
include "ctop.mm"
include "wb.mm"
include "retop.mm"
include "iccssre.mm"
include "uniretop.mm"
include "cmpsub.mm"
include "mpbid.mm"
include "adantr.mm"
include "simprr.mm"
include "unieq.mm"
include "sseq2d.mm"
include "pweq.mm"
include "ineq1d.mm"
include "rexeqdv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "wex.mm"
include "simprl.mm"
include "elin.mm"
include "simprd.mm"
include "simpld.mm"
include "elpwid.mm"
include "sseld.mm"
include "fvelrnb.mm"
include "sylibd.mm"
include "ralrimiv.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "ac6sfi.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "ad2antrr.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprrl.mm"
include "simprrr.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "ovolicc2lem5.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "rexlimdvaa.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "resubcld.mm"
include "rexrd.mm"
include "infxrgelb.mm"
include "mpbird.mm"
include "ovolval.mm"
include "breqtrrd.mm"

theorem ovolicc2
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cM: class M
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vz: setvar z
  let cH: class H
  let cC: class C
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cK: class K
  let cG: class G
  let cW: class W
  let cP: class P
  let cT: class T
  let cN: class N
  let cS: class S
  let cU: class U
  let cX: class X
  assume ovolicc.1: |- ( ph -> A e. RR )
  assume ovolicc.2: |- ( ph -> B e. RR )
  assume ovolicc.3: |- ( ph -> A <_ B )
  assume ovolicc2.m: |- M = { y e. RR* | E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( ( A [,] B ) C_ U. ran ( (,) o. f ) /\ y = sup ( ran seq 1 ( + , ( ( abs o. - ) o. f ) ) , RR* , < ) ) }

  disjoint f y
  disjoint A f
  disjoint A y
  disjoint B f
  disjoint B y
  disjoint M y
  disjoint f ph
  disjoint ph y
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f z
  disjoint g h
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint B g
  disjoint B h
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B t
  disjoint B u
  disjoint B v
  disjoint B x
  disjoint B z
  disjoint H t
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint C y
  disjoint C z
  disjoint h i
  disjoint h j
  disjoint F h
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint F i
  disjoint j k
  disjoint j n
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F t
  disjoint F x
  disjoint F y
  disjoint i u
  disjoint i z
  disjoint K i
  disjoint j u
  disjoint j z
  disjoint K j
  disjoint K k
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint f i
  disjoint f j
  disjoint G f
  disjoint G h
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint G n
  disjoint G t
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint i m
  disjoint M i
  disjoint j m
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M t
  disjoint M x
  disjoint M z
  disjoint W i
  disjoint W j
  disjoint W k
  disjoint W m
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint P k
  disjoint P y
  disjoint g i
  disjoint g j
  disjoint g ph
  disjoint h ph
  disjoint i v
  disjoint i ph
  disjoint j v
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph t
  disjoint ph v
  disjoint ph x
  disjoint ph z
  disjoint T f
  disjoint T h
  disjoint T k
  disjoint T n
  disjoint T t
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint N k
  disjoint N n
  disjoint N t
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint S h
  disjoint S z
  disjoint U h
  disjoint U n
  disjoint U t
  disjoint U u
  disjoint U x
  disjoint U z
  disjoint X t
  assert |- ( ph -> ( B - A ) <_ ( vol* ` ( A [,] B ) ) )

  proof
    wph
    cB
    cA
    cmin
    co
    #
    cM
    cxr
    clt
    cinf
    #
    cA
    cB
    cicc
    co
    #
    covol
    cfv
    #
    cle
    wph
    @0
    @1
    cle
    wbr
    #
    @0
    vz
    cv
    #
    cle
    wbr
    #
    vz
    cM
    wral
    #
    wph
    @6
    vz
    cM
    @5
    cM
    wcel
    @2
    cioo
    vf
    cv
    #
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    @5
    caddc
    cabs
    cmin
    ccom
    @8
    ccom
    c1
    cseq
    #
    crn
    cxr
    clt
    csup
    #
    wceq
    #
    wa
    #
    vf
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cn
    cmap
    co
    #
    wrex
    wph
    @6
    vy
    @2
    @5
    vf
    cM
    ovolicc2.m
    elovolm
    wph
    @16
    @6
    vf
    @19
    wph
    @8
    @19
    wcel
    #
    wa
    #
    @12
    @15
    @6
    wph
    @20
    @12
    @15
    @6
    wi
    wph
    @20
    @12
    wa
    #
    wa
    #
    @6
    @15
    @0
    @14
    cle
    wbr
    #
    @23
    @2
    vv
    cv
    #
    cuni
    wss
    #
    vv
    @10
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @24
    @23
    @10
    cioo
    crn
    #
    ctg
    cfv
    #
    cpw
    #
    wcel
    #
    @2
    vu
    cv
    #
    cuni
    #
    wss
    #
    @26
    vv
    @34
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vu
    @32
    wral
    #
    @12
    @29
    @23
    @10
    @31
    wss
    @33
    @23
    @10
    @30
    @31
    @23
    cn
    @30
    @9
    wf
    #
    @10
    @30
    wss
    wph
    @20
    @42
    @12
    @21
    cxr
    cxr
    cxp
    #
    @30
    cioo
    wf
    #
    cn
    @43
    @8
    wf
    #
    @42
    cioo
    @43
    wfn
    #
    @44
    @43
    cr
    cpw
    #
    cioo
    wf
    @46
    ioof
    @43
    @47
    cioo
    ffn
    ax-mp
    @43
    cioo
    dffn3
    mpbi
    @21
    cn
    @18
    @8
    wf
    #
    @18
    @43
    wss
    @45
    @21
    @20
    @48
    wph
    @20
    simpr
    @18
    cn
    @8
    @17
    cle
    cr
    cr
    reex
    reex
    xpex
    inex2
    nnex
    elmap
    sylib
    #
    @18
    @17
    @43
    cle
    @17
    inss2
    rexpssxrxp
    sstri
    cn
    @18
    @43
    @8
    fss
    sylancl
    cn
    @43
    @30
    cioo
    @8
    fco
    sylancr
    #
    adantrr
    cn
    @30
    @9
    frn
    syl
    @30
    ctb
    wcel
    @30
    @31
    wss
    retopbas
    @30
    ctb
    bastg
    ax-mp
    syl6ss
    @10
    @31
    @30
    ctg
    fvex
    elpw2
    sylibr
    wph
    @41
    @22
    wph
    @31
    @2
    crest
    co
    #
    ccmp
    wcel
    #
    @41
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @52
    ovolicc.1
    ovolicc.2
    cA
    cB
    @51
    @31
    @31
    eqid
    @51
    eqid
    icccmp
    syl2anc
    wph
    @31
    ctop
    wcel
    @2
    cr
    wss
    #
    @52
    @41
    wb
    retop
    wph
    @53
    @54
    @55
    ovolicc.1
    ovolicc.2
    cA
    cB
    iccssre
    syl2anc
    #
    @2
    @31
    cr
    vu
    vv
    uniretop
    cmpsub
    sylancr
    mpbid
    adantr
    wph
    @20
    @12
    simprr
    @40
    @12
    @29
    wi
    vu
    @10
    @32
    @34
    @10
    wceq
    #
    @36
    @12
    @39
    @29
    @57
    @35
    @11
    @2
    @34
    @10
    unieq
    sseq2d
    @57
    @26
    vv
    @38
    @28
    @57
    @37
    @27
    cfn
    @34
    @10
    pweq
    ineq1d
    rexeqdv
    imbi12d
    rspcv
    syl3c
    wph
    @20
    @29
    @24
    wi
    @12
    @21
    @26
    @24
    vv
    @28
    @21
    @25
    @28
    wcel
    #
    @26
    wa
    #
    wa
    #
    @25
    cn
    vg
    cv
    #
    wf
    #
    vt
    cv
    #
    @61
    cfv
    #
    @9
    cfv
    #
    @63
    wceq
    #
    vt
    @25
    wral
    #
    wa
    #
    vg
    wex
    #
    @24
    @60
    @25
    cfn
    wcel
    #
    vk
    cv
    #
    @9
    cfv
    #
    @63
    wceq
    #
    vk
    cn
    wrex
    #
    vt
    @25
    wral
    @69
    @60
    @25
    @27
    wcel
    #
    @70
    @60
    @58
    @75
    @70
    wa
    @21
    @58
    @26
    simprl
    @25
    @27
    cfn
    elin
    sylib
    #
    simprd
    @60
    @74
    vt
    @25
    @60
    @63
    @25
    wcel
    @63
    @10
    wcel
    #
    @74
    @60
    @25
    @10
    @63
    @60
    @25
    @10
    @60
    @75
    @70
    @76
    simpld
    elpwid
    sseld
    @60
    @9
    cn
    wfn
    #
    @77
    @74
    wb
    @21
    @78
    @59
    @21
    @42
    @78
    @50
    cn
    @30
    @9
    ffn
    syl
    adantr
    vk
    cn
    @63
    @9
    fvelrnb
    syl
    sylibd
    ralrimiv
    @73
    @66
    vt
    vk
    @25
    cn
    vg
    @71
    @64
    wceq
    @72
    @65
    @63
    @71
    @64
    @9
    fveq2
    eqeq1d
    ac6sfi
    syl2anc
    @60
    @68
    @24
    vg
    @21
    @59
    @68
    @24
    @21
    @59
    @68
    wa
    #
    wa
    #
    vu
    vx
    cA
    cB
    @13
    @34
    @2
    cin
    c0
    wne
    vu
    @25
    crab
    #
    @25
    @8
    @61
    wph
    @53
    @20
    @79
    ovolicc.1
    ad2antrr
    wph
    @54
    @20
    @79
    ovolicc.2
    ad2antrr
    wph
    cA
    cB
    cle
    wbr
    @20
    @79
    ovolicc.3
    ad2antrr
    @13
    eqid
    @21
    @48
    @79
    @49
    adantr
    @21
    @58
    @26
    @68
    simprll
    @21
    @58
    @26
    @68
    simprlr
    @21
    @59
    @62
    @67
    simprrl
    @80
    @67
    vx
    cv
    #
    @25
    wcel
    @82
    @61
    cfv
    #
    @9
    cfv
    #
    @82
    wceq
    #
    @21
    @59
    @62
    @67
    simprrr
    @66
    @85
    vt
    @82
    @25
    @63
    @82
    wceq
    #
    @65
    @84
    @63
    @82
    @86
    @64
    @83
    @9
    @63
    @82
    @61
    fveq2
    fveq2d
    @86
    id
    eqeq12d
    rspccva
    sylan
    @81
    eqid
    ovolicc2lem5
    expr
    exlimdv
    mpd
    rexlimdvaa
    adantrr
    mpd
    @5
    @14
    @0
    cle
    breq2
    syl5ibrcom
    expr
    impd
    rexlimdva
    syl5bi
    ralrimiv
    wph
    cM
    cxr
    wss
    @0
    cxr
    wcel
    @4
    @7
    wb
    cM
    @12
    vy
    cv
    @14
    wceq
    wa
    vf
    @19
    wrex
    #
    vy
    cxr
    crab
    cxr
    ovolicc2.m
    @87
    vy
    cxr
    ssrab2
    eqsstri
    wph
    @0
    wph
    cB
    cA
    ovolicc.2
    ovolicc.1
    resubcld
    rexrd
    vz
    cM
    @0
    infxrgelb
    sylancr
    mpbird
    wph
    @55
    @3
    @1
    wceq
    @56
    vy
    @2
    vf
    cM
    ovolicc2.m
    ovolval
    syl
    breqtrrd
end
