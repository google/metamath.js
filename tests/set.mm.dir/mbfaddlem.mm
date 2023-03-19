include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cr.mm"
include "cvol.mm"
include "cdm.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "readdcl.mm"
include "adantl.mm"
include "wf.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "cmbf.mm"
include "mbfdm.mm"
include "eqeltrrd.mm"
include "inidm.mm"
include "off.mm"
include "cq.mm"
include "ccnv.mm"
include "cpnf.mm"
include "cioo.mm"
include "cima.mm"
include "cmin.mm"
include "cin.mm"
include "ciun.mm"
include "wrex.mm"
include "eliun.mm"
include "cfv.mm"
include "r19.42v.mm"
include "clt.mm"
include "wbr.mm"
include "simplr.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "ltsubaddd.mm"
include "wb.mm"
include "qre.mm"
include "ltsub23.mm"
include "syl3anc.mm"
include "anbi2d.mm"
include "ancom.mm"
include "syl6bb.mm"
include "rexbidva.mm"
include "wi.mm"
include "resubcld.mm"
include "lttr.mm"
include "rexlimdva.mm"
include "qbtwnre.mm"
include "3expia.mm"
include "syl2anc.mm"
include "impbid.mm"
include "bitrd.mm"
include "wfn.mm"
include "ffn.mm"
include "eqidd.mm"
include "ofval.mm"
include "breq2d.mm"
include "3bitr4d.mm"
include "cxr.mm"
include "rexrd.mm"
include "elioopnf.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "anbi12d.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "elpreima.mm"
include "elin.mm"
include "anandi.mm"
include "3bitr4g.mm"
include "rexbidv.mm"
include "eqrdv.mm"
include "cn.mm"
include "cdom.mm"
include "wral.mm"
include "cen.mm"
include "qnnen.mm"
include "endom.mm"
include "ax-mp.mm"
include "mbfima.mm"
include "inmbl.mm"
include "ad2antrr.mm"
include "ralrimiva.mm"
include "iunmbl2.mm"
include "sylancr.mm"
include "ismbf3d.mm"

theorem mbfaddlem
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cG: class G
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume mbfadd.1: |- ( ph -> F e. MblFn )
  assume mbfadd.2: |- ( ph -> G e. MblFn )
  assume mbfadd.3: |- ( ph -> F : A --> RR )
  assume mbfadd.4: |- ( ph -> G : A --> RR )


  assert |- ( ph -> ( F oF + G ) e. MblFn )

  proof
    wph
    vy
    cA
    cF
    cG
    caddc
    cof
    co
    #
    wph
    vx
    vy
    cA
    cA
    cA
    caddc
    cr
    cr
    cr
    cF
    cG
    cvol
    cdm
    #
    @1
    vx
    cv
    #
    cr
    wcel
    vy
    cv
    #
    cr
    wcel
    #
    wa
    @2
    @3
    caddc
    co
    cr
    wcel
    wph
    @2
    @3
    readdcl
    adantl
    mbfadd.3
    mbfadd.4
    wph
    cF
    cdm
    #
    cA
    @1
    wph
    cA
    cr
    cF
    wf
    #
    @5
    cA
    wceq
    mbfadd.3
    cA
    cr
    cF
    fdm
    syl
    wph
    cF
    cmbf
    wcel
    #
    @5
    @1
    wcel
    mbfadd.1
    cF
    mbfdm
    syl
    eqeltrrd
    #
    @8
    cA
    inidm
    #
    off
    #
    wph
    @4
    wa
    #
    vr
    cq
    cF
    ccnv
    vr
    cv
    #
    cpnf
    cioo
    co
    #
    cima
    #
    cG
    ccnv
    @3
    @12
    cmin
    co
    #
    cpnf
    cioo
    co
    #
    cima
    #
    cin
    #
    ciun
    #
    @0
    ccnv
    @3
    cpnf
    cioo
    co
    #
    cima
    #
    @1
    @11
    vx
    @19
    @21
    @2
    @19
    wcel
    @2
    @18
    wcel
    #
    vr
    cq
    wrex
    #
    @11
    @2
    @21
    wcel
    #
    vr
    @2
    cq
    @18
    eliun
    @11
    @2
    cA
    wcel
    #
    @2
    cF
    cfv
    #
    @13
    wcel
    #
    @2
    cG
    cfv
    #
    @16
    wcel
    #
    wa
    #
    wa
    #
    vr
    cq
    wrex
    #
    @25
    @2
    @0
    cfv
    #
    @20
    wcel
    #
    wa
    #
    @23
    @24
    @32
    @25
    @30
    vr
    cq
    wrex
    #
    wa
    @11
    @35
    @25
    @30
    vr
    cq
    r19.42v
    @11
    @25
    @36
    @34
    @11
    @25
    wa
    #
    @12
    @26
    clt
    wbr
    #
    @15
    @28
    clt
    wbr
    #
    wa
    #
    vr
    cq
    wrex
    #
    @3
    @33
    clt
    wbr
    #
    @36
    @34
    @37
    @3
    @28
    cmin
    co
    #
    @26
    clt
    wbr
    #
    @3
    @26
    @28
    caddc
    co
    #
    clt
    wbr
    @41
    @42
    @37
    @3
    @28
    @26
    wph
    @4
    @25
    simplr
    #
    @11
    cA
    cr
    @2
    cG
    wph
    cA
    cr
    cG
    wf
    #
    @4
    mbfadd.4
    adantr
    ffvelrnda
    #
    @11
    cA
    cr
    @2
    cF
    wph
    @6
    @4
    mbfadd.3
    adantr
    ffvelrnda
    #
    ltsubaddd
    @37
    @41
    @43
    @12
    clt
    wbr
    #
    @38
    wa
    #
    vr
    cq
    wrex
    #
    @44
    @37
    @40
    @51
    vr
    cq
    @37
    @12
    cq
    wcel
    #
    wa
    #
    @40
    @38
    @50
    wa
    @51
    @54
    @39
    @50
    @38
    @54
    @4
    @12
    cr
    wcel
    #
    @28
    cr
    wcel
    #
    @39
    @50
    wb
    @37
    @4
    @53
    @46
    adantr
    #
    @53
    @55
    @37
    @12
    qre
    adantl
    #
    @37
    @56
    @53
    @48
    adantr
    #
    @3
    @12
    @28
    ltsub23
    syl3anc
    anbi2d
    @38
    @50
    ancom
    syl6bb
    rexbidva
    @37
    @52
    @44
    @37
    @51
    @44
    vr
    cq
    @54
    @43
    cr
    wcel
    #
    @55
    @26
    cr
    wcel
    #
    @51
    @44
    wi
    @37
    @60
    @53
    @37
    @3
    @28
    @46
    @48
    resubcld
    #
    adantr
    @58
    @37
    @61
    @53
    @49
    adantr
    #
    @43
    @12
    @26
    lttr
    syl3anc
    rexlimdva
    @37
    @60
    @61
    @44
    @52
    wi
    @62
    @49
    @60
    @61
    @44
    @52
    vr
    @43
    @26
    qbtwnre
    3expia
    syl2anc
    impbid
    bitrd
    @37
    @33
    @45
    @3
    clt
    @11
    cA
    cA
    @26
    @28
    caddc
    cA
    cF
    cG
    @1
    @1
    @2
    wph
    cF
    cA
    wfn
    #
    @4
    wph
    @6
    @64
    mbfadd.3
    cA
    cr
    cF
    ffn
    syl
    adantr
    #
    wph
    cG
    cA
    wfn
    #
    @4
    wph
    @47
    @66
    mbfadd.4
    cA
    cr
    cG
    ffn
    syl
    adantr
    #
    wph
    cA
    @1
    wcel
    @4
    @8
    adantr
    #
    @68
    @9
    @37
    @26
    eqidd
    @37
    @28
    eqidd
    ofval
    breq2d
    3bitr4d
    @37
    @30
    @40
    vr
    cq
    @54
    @27
    @38
    @29
    @39
    @54
    @27
    @61
    @38
    wa
    #
    @38
    @54
    @12
    cxr
    wcel
    @27
    @69
    wb
    @54
    @12
    @58
    rexrd
    @12
    @26
    elioopnf
    syl
    @54
    @61
    @38
    @63
    biantrurd
    bitr4d
    @54
    @29
    @56
    @39
    wa
    #
    @39
    @54
    @15
    cxr
    wcel
    @29
    @70
    wb
    @54
    @15
    @54
    @3
    @12
    @57
    @58
    resubcld
    rexrd
    @15
    @28
    elioopnf
    syl
    @54
    @56
    @39
    @59
    biantrurd
    bitr4d
    anbi12d
    rexbidva
    @37
    @34
    @33
    cr
    wcel
    #
    @42
    wa
    #
    @42
    @37
    @3
    cxr
    wcel
    @34
    @72
    wb
    @37
    @3
    @46
    rexrd
    @3
    @33
    elioopnf
    syl
    @37
    @71
    @42
    @11
    cA
    cr
    @2
    @0
    wph
    cA
    cr
    @0
    wf
    #
    @4
    @10
    adantr
    ffvelrnda
    biantrurd
    bitr4d
    3bitr4d
    pm5.32da
    syl5bb
    @11
    @22
    @31
    vr
    cq
    @11
    @2
    @14
    wcel
    #
    @2
    @17
    wcel
    #
    wa
    @25
    @27
    wa
    #
    @25
    @29
    wa
    #
    wa
    @22
    @31
    @11
    @74
    @76
    @75
    @77
    @11
    @64
    @74
    @76
    wb
    @65
    cA
    @2
    @13
    cF
    elpreima
    syl
    @11
    @66
    @75
    @77
    wb
    @67
    cA
    @2
    @16
    cG
    elpreima
    syl
    anbi12d
    @2
    @14
    @17
    elin
    @25
    @27
    @29
    anandi
    3bitr4g
    rexbidv
    @11
    @0
    cA
    wfn
    #
    @24
    @35
    wb
    wph
    @78
    @4
    wph
    @73
    @78
    @10
    cA
    cr
    @0
    ffn
    syl
    adantr
    cA
    @2
    @20
    @0
    elpreima
    syl
    3bitr4d
    syl5bb
    eqrdv
    @11
    cq
    cn
    cdom
    wbr
    #
    @18
    @1
    wcel
    #
    vr
    cq
    wral
    @19
    @1
    wcel
    cq
    cn
    cen
    wbr
    @79
    qnnen
    cq
    cn
    endom
    ax-mp
    @11
    @80
    vr
    cq
    wph
    @80
    @4
    @53
    wph
    @14
    @1
    wcel
    #
    @17
    @1
    wcel
    #
    @80
    wph
    @7
    @6
    @81
    mbfadd.1
    mbfadd.3
    cA
    @12
    cpnf
    cF
    mbfima
    syl2anc
    wph
    cG
    cmbf
    wcel
    @47
    @82
    mbfadd.2
    mbfadd.4
    cA
    @15
    cpnf
    cG
    mbfima
    syl2anc
    @14
    @17
    inmbl
    syl2anc
    ad2antrr
    ralrimiva
    cq
    @18
    vr
    iunmbl2
    sylancr
    eqeltrrd
    ismbf3d
end
