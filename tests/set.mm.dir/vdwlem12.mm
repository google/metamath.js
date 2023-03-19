include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "csdm.mm"
include "wbr.mm"
include "clt.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "hashcl.mm"
include "syl.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "wceq.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "breqtrrd.mm"
include "wb.mm"
include "fzfi.mm"
include "hashsdom.mm"
include "sylancl.mm"
include "mpbid.mm"
include "cdom.mm"
include "wn.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "fveq2.mm"
include "eqeqan12d.mm"
include "eqeq12.mm"
include "imbi12d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "cr.mm"
include "wss.mm"
include "elfznn.mm"
include "nnred.mm"
include "ssriv.mm"
include "a1i.mm"
include "biidd.mm"
include "cle.mm"
include "w3a.mm"
include "simplr3.mm"
include "c2.mm"
include "cvdwm.mm"
include "ad2antrr.mm"
include "3simpa.mm"
include "cvdwa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wrex.mm"
include "wex.mm"
include "cmin.mm"
include "simplrl.mm"
include "simprr.mm"
include "simplrr.mm"
include "nnsub.mm"
include "syl2anc.mm"
include "cun.mm"
include "df-2.mm"
include "fveq2i.mm"
include "oveqi.mm"
include "1nn0.mm"
include "vdwapun.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "simprl.mm"
include "wfn.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mpbir2and.mm"
include "snssd.mm"
include "nncnd.mm"
include "pncan3d.mm"
include "oveq1d.mm"
include "vdwap1.mm"
include "eqtrd.mm"
include "eqidd.mm"
include "eqsstrd.mm"
include "unssd.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "fvex.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "sseq2d.mm"
include "2rexbidv.mm"
include "spcev.mm"
include "ovex.mm"
include "2nn0.mm"
include "vdwmc.mm"
include "mpbird.mm"
include "sylanl2.mm"
include "expr.mm"
include "mtod.mm"
include "simplr1.mm"
include "simplr2.mm"
include "sseldi.mm"
include "eqleltd.mm"
include "ex.mm"
include "wlogle.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "f1domg.mm"
include "sylc.mm"
include "domnsym.mm"
include "pm2.65i.mm"

theorem vdwlem12
  let wph: wff ph
  let cR: class R
  let cF: class F
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vs: setvar s
  let cK: class K
  let cM: class M
  let cH: class H
  assume vdw.r: |- ( ph -> R e. Fin )
  assume vdwlem12.f: |- ( ph -> F : ( 1 ... ( ( # ` R ) + 1 ) ) --> R )
  assume vdwlem12.2: |- ( ph -> -. 2 MonoAP F )


  assert |- -. ph

  proof
    wph
    cR
    c1
    cR
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cfz
    co
    #
    csdm
    wbr
    #
    wph
    @0
    @2
    chash
    cfv
    #
    clt
    wbr
    #
    @3
    wph
    @0
    @1
    @4
    clt
    wph
    @0
    wph
    @0
    wph
    cR
    cfn
    wcel
    #
    @0
    cn0
    wcel
    #
    vdw.r
    cR
    hashcl
    syl
    #
    nn0red
    ltp1d
    wph
    @1
    cn0
    wcel
    @4
    @1
    wceq
    wph
    @1
    wph
    @7
    @1
    cn
    wcel
    @8
    @0
    nn0p1nn
    syl
    nnnn0d
    @1
    hashfz1
    syl
    breqtrrd
    wph
    @6
    @2
    cfn
    wcel
    @5
    @3
    wb
    vdw.r
    c1
    @1
    fzfi
    cR
    @2
    hashsdom
    sylancl
    mpbid
    wph
    @2
    cR
    cdom
    wbr
    #
    @3
    wn
    wph
    @6
    @2
    cR
    cF
    wf1
    #
    @9
    vdw.r
    wph
    @2
    cR
    cF
    wf
    #
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
    @2
    wral
    vx
    @2
    wral
    @10
    vdwlem12.f
    wph
    @18
    vx
    vy
    @2
    @2
    wph
    vz
    cv
    #
    cF
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vz
    vw
    weq
    #
    wi
    @18
    @18
    vx
    vy
    vz
    vw
    @2
    vz
    vx
    weq
    #
    vw
    vy
    weq
    #
    wa
    @23
    @16
    @24
    @17
    @25
    @26
    @20
    @13
    @22
    @15
    @19
    @12
    cF
    fveq2
    @21
    @14
    cF
    fveq2
    eqeqan12d
    @19
    @12
    @21
    @14
    eqeq12
    imbi12d
    vz
    vy
    weq
    #
    vw
    vx
    weq
    #
    wa
    #
    @23
    @16
    @24
    @17
    @29
    @23
    @15
    @13
    wceq
    @16
    @27
    @28
    @20
    @15
    @22
    @13
    @19
    @14
    cF
    fveq2
    @21
    @12
    cF
    fveq2
    eqeqan12d
    @15
    @13
    eqcom
    syl6bb
    @29
    @24
    vy
    vx
    weq
    @17
    @19
    @14
    @21
    @12
    eqeq12
    @14
    @12
    eqcom
    syl6bb
    imbi12d
    @2
    cr
    wss
    wph
    vx
    @2
    cr
    @12
    @2
    wcel
    #
    @12
    @12
    @1
    elfznn
    #
    nnred
    #
    ssriv
    #
    a1i
    wph
    @30
    @14
    @2
    wcel
    #
    wa
    #
    wa
    #
    @18
    biidd
    wph
    @30
    @34
    @12
    @14
    cle
    wbr
    #
    w3a
    #
    wa
    #
    @16
    @17
    @39
    @16
    wa
    #
    @17
    @37
    @12
    @14
    clt
    wbr
    #
    wn
    @30
    @34
    @37
    wph
    @16
    simplr3
    @40
    @41
    c2
    cF
    cvdwm
    wbr
    #
    wph
    @42
    wn
    @38
    @16
    vdwlem12.2
    ad2antrr
    @39
    @16
    @41
    @42
    @38
    wph
    @35
    @16
    @41
    wa
    #
    @42
    @30
    @34
    @37
    3simpa
    @36
    @43
    wa
    #
    @42
    va
    cv
    #
    vd
    cv
    #
    c2
    cvdwa
    cfv
    #
    co
    #
    cF
    ccnv
    #
    vc
    cv
    #
    csn
    #
    cima
    #
    wss
    #
    vd
    cn
    wrex
    va
    cn
    wrex
    #
    vc
    wex
    #
    @44
    @48
    @49
    @15
    csn
    #
    cima
    #
    wss
    #
    vd
    cn
    wrex
    va
    cn
    wrex
    #
    @55
    @44
    @12
    cn
    wcel
    #
    @14
    @12
    cmin
    co
    #
    cn
    wcel
    #
    @12
    @61
    @47
    co
    #
    @57
    wss
    #
    @59
    @44
    @30
    @60
    wph
    @30
    @34
    @43
    simplrl
    #
    @31
    syl
    #
    @44
    @41
    @62
    @36
    @16
    @41
    simprr
    @44
    @60
    @14
    cn
    wcel
    #
    @41
    @62
    wb
    @66
    @44
    @34
    @67
    wph
    @30
    @34
    @43
    simplrr
    #
    @14
    @1
    elfznn
    syl
    #
    @12
    @14
    nnsub
    syl2anc
    mpbid
    #
    @44
    @63
    @12
    csn
    #
    @12
    @61
    caddc
    co
    #
    @61
    c1
    cvdwa
    cfv
    #
    co
    #
    cun
    #
    @57
    @44
    @63
    @12
    @61
    c1
    c1
    caddc
    co
    #
    cvdwa
    cfv
    #
    co
    #
    @75
    @47
    @77
    @12
    @61
    c2
    @76
    cvdwa
    df-2
    fveq2i
    oveqi
    @44
    c1
    cn0
    wcel
    #
    @60
    @62
    @78
    @75
    wceq
    @79
    @44
    1nn0
    a1i
    @66
    @70
    @12
    @61
    c1
    vdwapun
    syl3anc
    syl5eq
    @44
    @71
    @74
    @57
    @44
    @12
    @57
    @44
    @12
    @57
    wcel
    #
    @30
    @16
    @65
    @36
    @16
    @41
    simprl
    @44
    cF
    @2
    wfn
    #
    @80
    @30
    @16
    wa
    wb
    @44
    @11
    @81
    wph
    @11
    @35
    @43
    vdwlem12.f
    ad2antrr
    #
    @2
    cR
    cF
    ffn
    syl
    #
    @2
    @15
    @12
    cF
    fniniseg
    syl
    mpbir2and
    snssd
    @44
    @74
    @14
    csn
    #
    @57
    @44
    @74
    @14
    @61
    @73
    co
    #
    @84
    @44
    @72
    @14
    @61
    @73
    @44
    @12
    @14
    @44
    @12
    @66
    nncnd
    @44
    @14
    @69
    nncnd
    pncan3d
    oveq1d
    @44
    @67
    @62
    @85
    @84
    wceq
    @69
    @70
    @14
    @61
    vdwap1
    syl2anc
    eqtrd
    @44
    @14
    @57
    @44
    @14
    @57
    wcel
    #
    @34
    @15
    @15
    wceq
    #
    @68
    @44
    @15
    eqidd
    @44
    @81
    @86
    @34
    @87
    wa
    wb
    @83
    @2
    @15
    @14
    cF
    fniniseg
    syl
    mpbir2and
    snssd
    eqsstrd
    unssd
    eqsstrd
    @58
    @64
    @12
    @46
    @47
    co
    #
    @57
    wss
    va
    vd
    @12
    @61
    cn
    cn
    va
    vx
    weq
    @48
    @88
    @57
    @45
    @12
    @46
    @47
    oveq1
    sseq1d
    @46
    @61
    wceq
    @88
    @63
    @57
    @46
    @61
    @12
    @47
    oveq2
    sseq1d
    rspc2ev
    syl3anc
    @54
    @59
    vc
    @15
    @14
    cF
    fvex
    @50
    @15
    wceq
    #
    @53
    @58
    va
    vd
    cn
    cn
    @89
    @52
    @57
    @48
    @89
    @51
    @56
    @49
    @50
    @15
    sneq
    imaeq2d
    sseq2d
    2rexbidv
    spcev
    syl
    @44
    cR
    cF
    c2
    @2
    va
    vc
    vd
    c1
    @1
    cfz
    ovex
    c2
    cn0
    wcel
    @44
    2nn0
    a1i
    @82
    vdwmc
    mpbird
    sylanl2
    expr
    mtod
    @40
    @12
    @14
    @40
    @30
    @12
    cr
    wcel
    @30
    @34
    @37
    wph
    @16
    simplr1
    @32
    syl
    @40
    @2
    cr
    @14
    @33
    @30
    @34
    @37
    wph
    @16
    simplr2
    sseldi
    eqleltd
    mpbir2and
    ex
    wlogle
    ralrimivva
    vx
    vy
    @2
    cR
    cF
    dff13
    sylanbrc
    @2
    cR
    cfn
    cF
    f1domg
    sylc
    @2
    cR
    domnsym
    syl
    pm2.65i
end
