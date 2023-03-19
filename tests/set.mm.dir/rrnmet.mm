include "cfn.mm"
include "wcel.mm"
include "cxp.mm"
include "cr.mm"
include "crrn.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cme.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cmpt2.mm"
include "simpl.mm"
include "cmap.mm"
include "simprl.mm"
include "syl6eleq.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "simprr.mm"
include "resubcld.mm"
include "resqcld.mm"
include "fsumrecl.mm"
include "sqge0d.mm"
include "fsumge0.mm"
include "resqrtcld.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "rrnval.mm"
include "feq1d.mm"
include "mpbird.mm"
include "sqrt00.mm"
include "syl2anc.mm"
include "fsum00.mm"
include "bitrd.mm"
include "cc.mm"
include "recnd.mm"
include "sqeq0.mm"
include "subeq0ad.mm"
include "ralbidva.mm"
include "rrnmval.mm"
include "3expb.mm"
include "eqeq1d.mm"
include "wfn.mm"
include "ffn.mm"
include "eqfnfv.mm"
include "3bitr4d.mm"
include "simpll.mm"
include "adantlr.mm"
include "simpr.mm"
include "trirn.mm"
include "npncand.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "fveq2d.mm"
include "sqsubswap.mm"
include "3brtr3d.mm"
include "adantr.mm"
include "w3a.mm"
include "3adant3r.mm"
include "3adant3l.mm"
include "oveq12d.mm"
include "3expa.mm"
include "an32s.mm"
include "3brtr4d.mm"
include "ralrimiva.mm"
include "jca.mm"
include "cvv.mm"
include "ovex.mm"
include "eqeltri.mm"
include "ismet.mm"
include "ax-mp.mm"
include "sylanbrc.mm"

theorem rrnmet
  let cI: class I
  let cX: class X
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vz: setvar z
  let cM: class M
  let wph: wff ph
  let cA: class A
  let cJ: class J
  let cP: class P
  let cR: class R
  let vt: setvar t
  let cF: class F
  assume rrnval.1: |- X = ( RR ^m I )


  assert |- ( I e. Fin -> ( Rn ` I ) e. ( Met ` X ) )

  proof
    cI
    cfn
    wcel
    #
    cX
    cX
    cxp
    #
    cr
    cI
    crrn
    cfv
    #
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    @2
    co
    #
    cc0
    wceq
    #
    @4
    @5
    wceq
    #
    wb
    #
    @6
    vz
    cv
    #
    @4
    @2
    co
    #
    @10
    @5
    @2
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    vz
    cX
    wral
    #
    wa
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @2
    cX
    cme
    cfv
    wcel
    #
    @0
    @3
    @1
    cr
    vx
    vy
    cX
    cX
    cI
    vk
    cv
    #
    @4
    cfv
    #
    @19
    @5
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    cmpt2
    #
    wf
    #
    @0
    @25
    cr
    wcel
    #
    vy
    cX
    wral
    vx
    cX
    wral
    @27
    @0
    @28
    vx
    vy
    cX
    cX
    @0
    @4
    cX
    wcel
    #
    @5
    cX
    wcel
    #
    wa
    #
    wa
    #
    @24
    @32
    cI
    @23
    vk
    @0
    @31
    simpl
    #
    @32
    @19
    cI
    wcel
    #
    wa
    #
    @22
    @35
    @20
    @21
    @32
    cI
    cr
    @19
    @4
    @32
    @4
    cr
    cI
    cmap
    co
    #
    wcel
    cI
    cr
    @4
    wf
    #
    @32
    @4
    cX
    @36
    @0
    @29
    @30
    simprl
    rrnval.1
    syl6eleq
    @4
    cr
    cI
    elmapi
    syl
    #
    ffvelrnda
    #
    @32
    cI
    cr
    @19
    @5
    @32
    @5
    @36
    wcel
    cI
    cr
    @5
    wf
    #
    @32
    @5
    cX
    @36
    @0
    @29
    @30
    simprr
    rrnval.1
    syl6eleq
    @5
    cr
    cI
    elmapi
    syl
    #
    ffvelrnda
    #
    resubcld
    #
    resqcld
    #
    fsumrecl
    #
    @32
    cI
    @23
    vk
    @33
    @44
    @35
    @22
    @43
    sqge0d
    #
    fsumge0
    #
    resqrtcld
    ralrimivva
    vx
    vy
    cX
    cX
    @25
    cr
    @26
    @26
    eqid
    fmpt2
    sylib
    @0
    @1
    cr
    @2
    @26
    vx
    vy
    vk
    cI
    cX
    rrnval.1
    rrnval
    feq1d
    mpbird
    @0
    @16
    vx
    vy
    cX
    cX
    @32
    @9
    @15
    @32
    @25
    cc0
    wceq
    #
    @20
    @21
    wceq
    #
    vk
    cI
    wral
    #
    @7
    @8
    @32
    @48
    @23
    cc0
    wceq
    #
    vk
    cI
    wral
    #
    @50
    @32
    @48
    @24
    cc0
    wceq
    #
    @52
    @32
    @24
    cr
    wcel
    cc0
    @24
    cle
    wbr
    @48
    @53
    wb
    @45
    @47
    @24
    sqrt00
    syl2anc
    @32
    cI
    @23
    vk
    @33
    @44
    @46
    fsum00
    bitrd
    @32
    @51
    @49
    vk
    cI
    @35
    @51
    @22
    cc0
    wceq
    #
    @49
    @35
    @22
    cc
    wcel
    @51
    @54
    wb
    @35
    @22
    @43
    recnd
    @22
    sqeq0
    syl
    @35
    @20
    @21
    @35
    @20
    @39
    recnd
    #
    @35
    @21
    @42
    recnd
    #
    subeq0ad
    bitrd
    ralbidva
    bitrd
    @32
    @6
    @25
    cc0
    @0
    @29
    @30
    @6
    @25
    wceq
    #
    vk
    @4
    @5
    cI
    cX
    rrnval.1
    rrnmval
    3expb
    #
    eqeq1d
    @32
    @4
    cI
    wfn
    #
    @5
    cI
    wfn
    #
    @8
    @50
    wb
    @32
    @37
    @59
    @38
    cI
    cr
    @4
    ffn
    syl
    @32
    @40
    @60
    @41
    cI
    cr
    @5
    ffn
    syl
    vk
    cI
    @4
    @5
    eqfnfv
    syl2anc
    3bitr4d
    @32
    @14
    vz
    cX
    @32
    @10
    cX
    wcel
    #
    wa
    #
    @25
    cI
    @19
    @10
    cfv
    #
    @20
    cmin
    co
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    cI
    @63
    @21
    cmin
    co
    #
    c2
    cexp
    co
    vk
    csu
    csqrt
    cfv
    #
    caddc
    co
    #
    @6
    @13
    cle
    @62
    cI
    @20
    @63
    cmin
    co
    #
    @67
    caddc
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    cI
    @70
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    @68
    caddc
    co
    @25
    @69
    cle
    @62
    cI
    @70
    @67
    vk
    @0
    @31
    @61
    simpll
    @62
    @34
    wa
    #
    @20
    @63
    @32
    @34
    @20
    cr
    wcel
    @61
    @39
    adantlr
    @62
    cI
    cr
    @19
    @10
    @62
    @10
    @36
    wcel
    cI
    cr
    @10
    wf
    @62
    @10
    cX
    @36
    @32
    @61
    simpr
    rrnval.1
    syl6eleq
    @10
    cr
    cI
    elmapi
    syl
    ffvelrnda
    #
    resubcld
    @77
    @63
    @21
    @78
    @32
    @34
    @21
    cr
    wcel
    @61
    @42
    adantlr
    resubcld
    trirn
    @62
    @73
    @24
    csqrt
    @62
    cI
    @72
    @23
    vk
    @77
    @71
    @22
    c2
    cexp
    @77
    @20
    @63
    @21
    @32
    @34
    @20
    cc
    wcel
    #
    @61
    @55
    adantlr
    #
    @77
    @63
    @78
    recnd
    #
    @32
    @34
    @21
    cc
    wcel
    @61
    @56
    adantlr
    npncand
    oveq1d
    sumeq2dv
    fveq2d
    @62
    @76
    @66
    @68
    caddc
    @62
    @75
    @65
    csqrt
    @62
    cI
    @74
    @64
    vk
    @77
    @79
    @63
    cc
    wcel
    @74
    @64
    wceq
    @80
    @81
    @20
    @63
    sqsubswap
    syl2anc
    sumeq2dv
    fveq2d
    oveq1d
    3brtr3d
    @32
    @57
    @61
    @58
    adantr
    @0
    @61
    @31
    @13
    @69
    wceq
    #
    @0
    @61
    @31
    @82
    @0
    @61
    @31
    w3a
    @11
    @66
    @12
    @68
    caddc
    @0
    @61
    @29
    @11
    @66
    wceq
    @30
    vk
    @10
    @4
    cI
    cX
    rrnval.1
    rrnmval
    3adant3r
    @0
    @61
    @30
    @12
    @68
    wceq
    @29
    vk
    @10
    @5
    cI
    cX
    rrnval.1
    rrnmval
    3adant3l
    oveq12d
    3expa
    an32s
    3brtr4d
    ralrimiva
    jca
    ralrimivva
    cX
    cvv
    wcel
    @18
    @3
    @17
    wa
    wb
    cX
    @36
    cvv
    rrnval.1
    cr
    cI
    cmap
    ovex
    eqeltri
    vx
    vy
    vz
    cvv
    @2
    cX
    ismet
    ax-mp
    sylanbrc
end
