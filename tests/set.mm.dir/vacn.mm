include "cnv.mm"
include "wcel.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "cba.mm"
include "cfv.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "eqid.mm"
include "nvgf.mm"
include "c2.mm"
include "cdiv.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "caddc.mm"
include "cr.mm"
include "cme.mm"
include "simplll.mm"
include "imsmet.mm"
include "syl.mm"
include "simplrl.mm"
include "adantr.mm"
include "simprl.mm"
include "metcl.mm"
include "syl3anc.mm"
include "simplrr.mm"
include "simprr.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lt2halves.mm"
include "cle.mm"
include "cnsb.mm"
include "cnmcv.mm"
include "nvmcl.mm"
include "nvtri.mm"
include "wceq.mm"
include "nvgcl.mm"
include "imsdval.mm"
include "nvaddsub4.mm"
include "syl122anc.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3brtr4d.mm"
include "readdcld.mm"
include "lelttr.mm"
include "mpand.mm"
include "syld.mm"
include "ralrimivva.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "cxmt.mm"
include "wb.mm"
include "imsxmet.mm"
include "txmetcn.mm"
include "mpbir2and.mm"

theorem vacn
  let cC: class C
  let cU: class U
  let cG: class G
  let cJ: class J
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume vacn.c: |- C = ( IndMet ` U )
  assume vacn.j: |- J = ( MetOpen ` C )
  assume vacn.g: |- G = ( +v ` U )


  assert |- ( U e. NrmCVec -> G e. ( ( J tX J ) Cn J ) )

  proof
    cU
    cnv
    wcel
    #
    cG
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    #
    cU
    cba
    cfv
    #
    @2
    cxp
    @2
    cG
    wf
    #
    vx
    cv
    #
    vz
    cv
    #
    cC
    co
    #
    vs
    cv
    #
    clt
    wbr
    #
    vy
    cv
    #
    vw
    cv
    #
    cC
    co
    #
    @7
    clt
    wbr
    #
    wa
    #
    @4
    @9
    cG
    co
    #
    @5
    @10
    cG
    co
    #
    cC
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    @2
    wral
    vz
    @2
    wral
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    #
    vy
    @2
    wral
    vx
    @2
    wral
    #
    cU
    cG
    @2
    @2
    eqid
    #
    vacn.g
    nvgf
    @0
    @22
    vx
    vy
    @2
    @2
    @0
    @4
    @2
    wcel
    #
    @9
    @2
    wcel
    #
    wa
    #
    wa
    #
    @21
    vr
    crp
    @28
    @17
    crp
    wcel
    #
    wa
    #
    @17
    c2
    cdiv
    co
    #
    crp
    wcel
    #
    @6
    @31
    clt
    wbr
    #
    @11
    @31
    clt
    wbr
    #
    wa
    #
    @18
    wi
    #
    vw
    @2
    wral
    vz
    @2
    wral
    #
    @21
    @29
    @32
    @28
    @17
    rphalfcl
    adantl
    @30
    @36
    vz
    vw
    @2
    @2
    @30
    @5
    @2
    wcel
    #
    @10
    @2
    wcel
    #
    wa
    #
    wa
    #
    @35
    @6
    @11
    caddc
    co
    #
    @17
    clt
    wbr
    #
    @18
    @41
    @6
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    @17
    cr
    wcel
    #
    @35
    @43
    wi
    @41
    cC
    @2
    cme
    cfv
    wcel
    #
    @25
    @38
    @44
    @41
    @0
    @47
    @0
    @27
    @29
    @40
    simplll
    #
    cC
    cU
    @2
    @24
    vacn.c
    imsmet
    syl
    #
    @30
    @25
    @40
    @0
    @25
    @26
    @29
    simplrl
    adantr
    #
    @30
    @38
    @39
    simprl
    #
    @4
    @5
    cC
    @2
    metcl
    syl3anc
    #
    @41
    @47
    @26
    @39
    @45
    @49
    @30
    @26
    @40
    @0
    @25
    @26
    @29
    simplrr
    adantr
    #
    @30
    @38
    @39
    simprr
    #
    @9
    @10
    cC
    @2
    metcl
    syl3anc
    #
    @29
    @46
    @28
    @40
    @17
    rpre
    ad2antlr
    #
    @6
    @11
    @17
    lt2halves
    syl3anc
    @41
    @16
    @42
    cle
    wbr
    #
    @43
    @18
    @41
    @4
    @5
    cU
    cnsb
    cfv
    #
    co
    #
    @9
    @10
    @58
    co
    #
    cG
    co
    #
    cU
    cnmcv
    cfv
    #
    cfv
    #
    @59
    @62
    cfv
    #
    @60
    @62
    cfv
    #
    caddc
    co
    #
    @16
    @42
    cle
    @41
    @0
    @59
    @2
    wcel
    #
    @60
    @2
    wcel
    #
    @63
    @66
    cle
    wbr
    @48
    @41
    @0
    @25
    @38
    @67
    @48
    @50
    @51
    @4
    @5
    cU
    @58
    @2
    @24
    @58
    eqid
    #
    nvmcl
    syl3anc
    @41
    @0
    @26
    @39
    @68
    @48
    @53
    @54
    @9
    @10
    cU
    @58
    @2
    @24
    @69
    nvmcl
    syl3anc
    @59
    @60
    cU
    cG
    @62
    @2
    @24
    vacn.g
    @62
    eqid
    #
    nvtri
    syl3anc
    @41
    @16
    @14
    @15
    @58
    co
    #
    @62
    cfv
    #
    @63
    @41
    @0
    @14
    @2
    wcel
    #
    @15
    @2
    wcel
    #
    @16
    @72
    wceq
    @48
    @41
    @0
    @25
    @26
    @73
    @48
    @50
    @53
    @4
    @9
    cU
    cG
    @2
    @24
    vacn.g
    nvgcl
    syl3anc
    #
    @41
    @0
    @38
    @39
    @74
    @48
    @51
    @54
    @5
    @10
    cU
    cG
    @2
    @24
    vacn.g
    nvgcl
    syl3anc
    #
    @14
    @15
    cC
    cU
    @58
    @62
    @2
    @24
    @69
    @70
    vacn.c
    imsdval
    syl3anc
    @41
    @71
    @61
    @62
    @41
    @0
    @25
    @26
    @38
    @39
    @71
    @61
    wceq
    @48
    @50
    @53
    @51
    @54
    @4
    @9
    @5
    @10
    cU
    cG
    @58
    @2
    @24
    vacn.g
    @69
    nvaddsub4
    syl122anc
    fveq2d
    eqtrd
    @41
    @6
    @64
    @11
    @65
    caddc
    @41
    @0
    @25
    @38
    @6
    @64
    wceq
    @48
    @50
    @51
    @4
    @5
    cC
    cU
    @58
    @62
    @2
    @24
    @69
    @70
    vacn.c
    imsdval
    syl3anc
    @41
    @0
    @26
    @39
    @11
    @65
    wceq
    @48
    @53
    @54
    @9
    @10
    cC
    cU
    @58
    @62
    @2
    @24
    @69
    @70
    vacn.c
    imsdval
    syl3anc
    oveq12d
    3brtr4d
    @41
    @16
    cr
    wcel
    #
    @42
    cr
    wcel
    @46
    @57
    @43
    wa
    @18
    wi
    @41
    @47
    @73
    @74
    @77
    @49
    @75
    @76
    @14
    @15
    cC
    @2
    metcl
    syl3anc
    @41
    @6
    @11
    @52
    @55
    readdcld
    @56
    @16
    @42
    @17
    lelttr
    syl3anc
    mpand
    syld
    ralrimivva
    @20
    @37
    vs
    @31
    crp
    @7
    @31
    wceq
    #
    @19
    @36
    vz
    vw
    @2
    @2
    @78
    @13
    @35
    @18
    @78
    @8
    @33
    @12
    @34
    @7
    @31
    @6
    clt
    breq2
    @7
    @31
    @11
    clt
    breq2
    anbi12d
    imbi1d
    2ralbidv
    rspcev
    syl2anc
    ralrimiva
    ralrimivva
    @0
    cC
    @2
    cxmt
    cfv
    wcel
    #
    @79
    @79
    @1
    @3
    @23
    wa
    wb
    cC
    cU
    @2
    @24
    vacn.c
    imsxmet
    #
    @80
    @80
    vx
    vy
    vr
    vs
    vw
    vz
    cC
    cC
    cC
    cG
    cJ
    cJ
    cJ
    @2
    @2
    @2
    vacn.j
    vacn.j
    vacn.j
    txmetcn
    syl3anc
    mpbir2and
end
