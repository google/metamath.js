include "cin.mm"
include "ccarsg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "elcarsg.mm"
include "mpbid.mm"
include "simpld.mm"
include "ssinss1.mm"
include "syl.mm"
include "cle.mm"
include "wbr.mm"
include "cxr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "elpwdifcl.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "elpwincl1.mm"
include "xaddcld.mm"
include "cun.mm"
include "indifundif.mm"
include "fveq2i.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "uneq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "uneq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "imp.mm"
include "syl21anc.mm"
include "syl5eqbrr.mm"
include "xleadd2a.mm"
include "syl31anc.mm"
include "simprd.mm"
include "wb.mm"
include "ineq1.mm"
include "difeq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "adantl.mm"
include "rspcdv.mm"
include "mpd.mm"
include "xrge0addass.mm"
include "syl3anc.mm"
include "inass.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "r19.21bi.mm"
include "3eqtr3d.mm"
include "breqtrd.mm"
include "inundif.mm"
include "jca.mm"
include "ffvelrnda.mm"
include "xrletri3.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ralrimiva.mm"

theorem inelcarsg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let ve: setvar e
  let vm: setvar m
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume difelcarsg.1: |- ( ph -> A e. ( toCaraSiga ` M ) )
  assume inelcarsg.1: |- ( ( ph /\ a e. ~P O /\ b e. ~P O ) -> ( M ` ( a u. b ) ) <_ ( ( M ` a ) +e ( M ` b ) ) )
  assume inelcarsg.2: |- ( ph -> B e. ( toCaraSiga ` M ) )

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint B b
  disjoint M a
  disjoint M b
  disjoint O a
  disjoint O b
  disjoint a ph
  disjoint b ph
  disjoint M a
  disjoint O a
  disjoint a ph
  disjoint A a
  disjoint A f
  disjoint a f
  disjoint b f
  disjoint B e
  disjoint B f
  disjoint a e
  disjoint b e
  disjoint e f
  disjoint M f
  disjoint O f
  disjoint f ph
  disjoint M e
  disjoint M m
  disjoint a e
  disjoint a m
  disjoint e m
  disjoint O e
  disjoint O m
  disjoint e ph
  disjoint m ph
  disjoint A e
  assert |- ( ph -> ( A i^i B ) e. ( toCaraSiga ` M ) )

  proof
    wph
    cA
    cB
    cin
    #
    cM
    ccarsg
    cfv
    #
    wcel
    @0
    cO
    wss
    #
    ve
    cv
    #
    @0
    cin
    #
    cM
    cfv
    #
    @3
    @0
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @3
    cM
    cfv
    #
    wceq
    #
    ve
    cO
    cpw
    #
    wral
    #
    wa
    wph
    @2
    @12
    wph
    cA
    cO
    wss
    #
    @2
    wph
    @13
    @3
    cA
    cin
    #
    cM
    cfv
    #
    @3
    cA
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @9
    wceq
    #
    ve
    @11
    wral
    #
    wph
    cA
    @1
    wcel
    @13
    @20
    wa
    difelcarsg.1
    wph
    cA
    ve
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    elcarsg
    mpbid
    #
    simpld
    cA
    cB
    cO
    ssinss1
    syl
    wph
    @10
    ve
    @11
    wph
    @3
    @11
    wcel
    #
    wa
    #
    @10
    @8
    @9
    cle
    wbr
    #
    @9
    @8
    cle
    wbr
    #
    wa
    #
    @23
    @24
    @25
    @23
    @8
    @5
    @14
    cB
    cdif
    #
    cM
    cfv
    #
    @17
    cxad
    co
    #
    cxad
    co
    #
    @9
    cle
    @23
    @7
    cxr
    wcel
    @29
    cxr
    wcel
    @5
    cxr
    wcel
    @7
    @29
    cle
    wbr
    @8
    @30
    cle
    wbr
    @23
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @7
    cc0
    cpnf
    iccssxr
    #
    @23
    @11
    @31
    @6
    cM
    wph
    @11
    @31
    cM
    wf
    @22
    carsgval.2
    adantr
    #
    @23
    @3
    @0
    cO
    wph
    @22
    simpr
    #
    elpwdifcl
    #
    ffvelrnd
    sseldi
    #
    @23
    @28
    @17
    @23
    @31
    cxr
    @28
    @32
    @23
    @11
    @31
    @27
    cM
    @33
    @23
    @14
    cB
    cO
    @23
    @3
    cA
    cO
    @34
    elpwincl1
    #
    elpwdifcl
    #
    ffvelrnd
    #
    sseldi
    @23
    @31
    cxr
    @17
    @32
    @23
    @11
    @31
    @16
    cM
    @33
    @23
    @3
    cA
    cO
    @34
    elpwdifcl
    #
    ffvelrnd
    #
    sseldi
    xaddcld
    @23
    @31
    cxr
    @5
    @32
    @23
    @11
    @31
    @4
    cM
    @33
    @23
    @3
    @0
    cO
    @34
    elpwincl1
    #
    ffvelrnd
    sseldi
    #
    @23
    @7
    @27
    @16
    cun
    #
    cM
    cfv
    #
    @29
    cle
    @44
    @6
    cM
    @3
    cA
    cB
    indifundif
    fveq2i
    @23
    @27
    @11
    wcel
    #
    @16
    @11
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cun
    #
    cM
    cfv
    #
    @48
    cM
    cfv
    #
    @49
    cM
    cfv
    #
    cxad
    co
    #
    cle
    wbr
    #
    vb
    @11
    wral
    va
    @11
    wral
    #
    @45
    @29
    cle
    wbr
    #
    @38
    @40
    wph
    @56
    @22
    wph
    @55
    va
    vb
    @11
    @11
    wph
    @48
    @11
    wcel
    @49
    @11
    wcel
    @55
    inelcarsg.1
    3expb
    ralrimivva
    adantr
    #
    @46
    @47
    wa
    @56
    @57
    @55
    @57
    @27
    @49
    cun
    #
    cM
    cfv
    #
    @28
    @53
    cxad
    co
    #
    cle
    wbr
    va
    vb
    @27
    @16
    @11
    @11
    @48
    @27
    wceq
    #
    @51
    @60
    @54
    @61
    cle
    @62
    @50
    @59
    cM
    @48
    @27
    @49
    uneq1
    fveq2d
    @62
    @52
    @28
    @53
    cxad
    @48
    @27
    cM
    fveq2
    oveq1d
    breq12d
    @49
    @16
    wceq
    #
    @60
    @45
    @61
    @29
    cle
    @63
    @59
    @44
    cM
    @49
    @16
    @27
    uneq2
    fveq2d
    @63
    @53
    @17
    @28
    cxad
    @49
    @16
    cM
    fveq2
    oveq2d
    breq12d
    rspc2v
    imp
    syl21anc
    syl5eqbrr
    @7
    @29
    @5
    xleadd2a
    syl31anc
    @23
    @14
    cB
    cin
    #
    cM
    cfv
    #
    @28
    cxad
    co
    #
    @17
    cxad
    co
    #
    @18
    @30
    @9
    @23
    @66
    @15
    @17
    cxad
    @23
    vf
    cv
    #
    cB
    cin
    #
    cM
    cfv
    #
    @68
    cB
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @68
    cM
    cfv
    #
    wceq
    #
    vf
    @11
    wral
    #
    @66
    @15
    wceq
    #
    wph
    @76
    @22
    wph
    cB
    cO
    wss
    #
    @76
    wph
    cB
    @1
    wcel
    @78
    @76
    wa
    inelcarsg.2
    wph
    cB
    vf
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    elcarsg
    mpbid
    simprd
    adantr
    @23
    @75
    @77
    vf
    @14
    @11
    @37
    @68
    @14
    wceq
    #
    @75
    @77
    wb
    @23
    @79
    @73
    @66
    @74
    @15
    @79
    @70
    @65
    @72
    @28
    cxad
    @79
    @69
    @64
    cM
    @68
    @14
    cB
    ineq1
    fveq2d
    @79
    @71
    @27
    cM
    @68
    @14
    cB
    difeq1
    fveq2d
    oveq12d
    @68
    @14
    cM
    fveq2
    eqeq12d
    adantl
    rspcdv
    mpd
    oveq1d
    @23
    @67
    @65
    @29
    cxad
    co
    #
    @30
    @23
    @65
    @31
    wcel
    @28
    @31
    wcel
    @17
    @31
    wcel
    @67
    @80
    wceq
    @23
    @11
    @31
    @64
    cM
    @33
    @23
    @14
    cB
    cO
    @37
    elpwincl1
    ffvelrnd
    @39
    @41
    @65
    @28
    @17
    xrge0addass
    syl3anc
    @65
    @5
    @29
    cxad
    @64
    @4
    cM
    @3
    cA
    cB
    inass
    fveq2i
    oveq1i
    syl6eq
    wph
    @19
    ve
    @11
    wph
    @13
    @20
    @21
    simprd
    r19.21bi
    3eqtr3d
    breqtrd
    @23
    @9
    @4
    @6
    cun
    #
    cM
    cfv
    #
    @8
    cle
    @81
    @3
    cM
    @3
    @0
    inundif
    fveq2i
    @23
    @4
    @11
    wcel
    #
    @6
    @11
    wcel
    #
    @56
    @82
    @8
    cle
    wbr
    #
    @42
    @35
    @58
    @83
    @84
    wa
    @56
    @85
    @55
    @85
    @4
    @49
    cun
    #
    cM
    cfv
    #
    @5
    @53
    cxad
    co
    #
    cle
    wbr
    va
    vb
    @4
    @6
    @11
    @11
    @48
    @4
    wceq
    #
    @51
    @87
    @54
    @88
    cle
    @89
    @50
    @86
    cM
    @48
    @4
    @49
    uneq1
    fveq2d
    @89
    @52
    @5
    @53
    cxad
    @48
    @4
    cM
    fveq2
    oveq1d
    breq12d
    @49
    @6
    wceq
    #
    @87
    @82
    @88
    @8
    cle
    @90
    @86
    @81
    cM
    @49
    @6
    @4
    uneq2
    fveq2d
    @90
    @53
    @7
    @5
    cxad
    @49
    @6
    cM
    fveq2
    oveq2d
    breq12d
    rspc2v
    imp
    syl21anc
    syl5eqbrr
    jca
    @23
    @8
    cxr
    wcel
    @9
    cxr
    wcel
    @10
    @26
    wb
    @23
    @5
    @7
    @43
    @36
    xaddcld
    @23
    @31
    cxr
    @9
    @32
    wph
    @11
    @31
    @3
    cM
    carsgval.2
    ffvelrnda
    sseldi
    @8
    @9
    xrletri3
    syl2anc
    mpbird
    ralrimiva
    jca
    wph
    @0
    ve
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    elcarsg
    mpbird
end
