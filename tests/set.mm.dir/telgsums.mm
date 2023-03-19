include "cn0.mm"
include "cv.mm"
include "csb.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cc0.mm"
include "cfz.mm"
include "cabl.mm"
include "wcel.mm"
include "ccmn.mm"
include "ablcmn.mm"
include "syl.mm"
include "wa.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "adantr.mm"
include "wral.mm"
include "simpr.mm"
include "rspcsbela.mm"
include "syl2anc.mm"
include "peano2nn0.mm"
include "syl2anr.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wsbc.mm"
include "rspsbca.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbcimg.mm"
include "sbcbr2g.mm"
include "csbvarg.mm"
include "breq2d.mm"
include "bitrd.mm"
include "sbceq1g.mm"
include "imbi12d.mm"
include "ax-mp.mm"
include "sylib.mm"
include "expcom.mm"
include "imp31.mm"
include "cr.mm"
include "nn0red.mm"
include "nn0re.mm"
include "ad2antlr.mm"
include "ltp1d.mm"
include "lttrd.mm"
include "ex.mm"
include "ovex.mm"
include "syld.mm"
include "imp.mm"
include "oveq12d.mm"
include "grpidcl.mm"
include "jccir.mm"
include "grpsubid.mm"
include "eqtrd.mm"
include "gsummptnn0fzv.mm"
include "wss.mm"
include "cuz.mm"
include "cfv.mm"
include "fzssuz.mm"
include "a1i.mm"
include "nn0uz.mm"
include "syl6sseqr.mm"
include "ssralv.mm"
include "sylc.mm"
include "telgsumfz0s.mm"
include "syl3c.mm"
include "oveq2d.mm"
include "0nn0.mm"
include "grpsubid1.mm"
include "3eqtrd.mm"

theorem telgsums
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cG: class G
  let c.mi: class .-
  let c.0: class .0.
  assume telgsums.b: |- B = ( Base ` G )
  assume telgsums.g: |- ( ph -> G e. Abel )
  assume telgsums.m: |- .- = ( -g ` G )
  assume telgsums.0: |- .0. = ( 0g ` G )
  assume telgsums.f: |- ( ph -> A. k e. NN0 C e. B )
  assume telgsums.s: |- ( ph -> S e. NN0 )
  assume telgsums.u: |- ( ph -> A. k e. NN0 ( S < k -> C = .0. ) )

  disjoint B i
  disjoint B k
  disjoint i k
  disjoint C i
  disjoint G i
  disjoint S i
  disjoint S k
  disjoint .0. i
  disjoint .0. k
  disjoint i ph
  disjoint .- i
  assert |- ( ph -> ( G gsum ( i e. NN0 |-> ( [_ i / k ]_ C .- [_ ( i + 1 ) / k ]_ C ) ) ) = [_ 0 / k ]_ C )

  proof
    wph
    cG
    vi
    cn0
    vk
    vi
    cv
    #
    cC
    csb
    #
    vk
    @0
    c1
    caddc
    co
    #
    cC
    csb
    #
    c.mi
    co
    #
    cmpt
    cgsu
    co
    cG
    vi
    cc0
    cS
    cfz
    co
    @4
    cmpt
    cgsu
    co
    vk
    cc0
    cC
    csb
    #
    vk
    cS
    c1
    caddc
    co
    #
    cC
    csb
    #
    c.mi
    co
    #
    @5
    wph
    cB
    @4
    cS
    vi
    cG
    c.0
    telgsums.b
    telgsums.0
    wph
    cG
    cabl
    wcel
    #
    cG
    ccmn
    wcel
    telgsums.g
    cG
    ablcmn
    syl
    wph
    @4
    cB
    wcel
    #
    vi
    cn0
    wph
    @0
    cn0
    wcel
    #
    wa
    #
    cG
    cgrp
    wcel
    #
    @1
    cB
    wcel
    #
    @3
    cB
    wcel
    #
    @10
    wph
    @13
    @11
    wph
    @9
    @13
    telgsums.g
    cG
    ablgrp
    syl
    #
    adantr
    #
    @12
    @11
    cC
    cB
    wcel
    #
    vk
    cn0
    wral
    #
    @14
    wph
    @11
    simpr
    wph
    @19
    @11
    telgsums.f
    adantr
    vk
    @0
    cn0
    cC
    cB
    rspcsbela
    syl2anc
    @11
    @2
    cn0
    wcel
    #
    @19
    @15
    wph
    @0
    peano2nn0
    #
    telgsums.f
    vk
    @2
    cn0
    cC
    cB
    rspcsbela
    syl2anr
    cB
    cG
    c.mi
    @1
    @3
    telgsums.b
    telgsums.m
    grpsubcl
    syl3anc
    ralrimiva
    telgsums.s
    wph
    cS
    @0
    clt
    wbr
    #
    @4
    c.0
    wceq
    #
    wi
    vi
    cn0
    @12
    @22
    @23
    @12
    @22
    wa
    #
    @4
    c.0
    c.0
    c.mi
    co
    #
    c.0
    @24
    @1
    c.0
    @3
    c.0
    c.mi
    wph
    @11
    @22
    @1
    c.0
    wceq
    #
    wph
    cS
    vk
    cv
    #
    clt
    wbr
    #
    cC
    c.0
    wceq
    #
    wi
    #
    vk
    cn0
    wral
    #
    @11
    @22
    @26
    wi
    #
    wi
    telgsums.u
    @11
    @31
    @32
    @11
    @31
    wa
    @30
    vk
    @0
    wsbc
    #
    @32
    @30
    vk
    @0
    cn0
    rspsbca
    @0
    cvv
    wcel
    #
    @33
    @32
    wb
    vi
    vex
    @34
    @33
    @28
    vk
    @0
    wsbc
    #
    @29
    vk
    @0
    wsbc
    #
    wi
    @32
    @28
    @29
    vk
    @0
    cvv
    sbcimg
    @34
    @35
    @22
    @36
    @26
    @34
    @35
    cS
    vk
    @0
    @27
    csb
    #
    clt
    wbr
    @22
    vk
    @0
    cS
    @27
    clt
    cvv
    sbcbr2g
    @34
    @37
    @0
    cS
    clt
    vk
    @0
    cvv
    csbvarg
    breq2d
    bitrd
    vk
    @0
    cC
    c.0
    cvv
    sbceq1g
    imbi12d
    bitrd
    ax-mp
    sylib
    expcom
    syl
    imp31
    @12
    @22
    @3
    c.0
    wceq
    #
    @12
    @22
    cS
    @2
    clt
    wbr
    #
    @38
    @12
    @22
    @39
    @24
    cS
    @0
    @2
    @12
    cS
    cr
    wcel
    #
    @22
    wph
    @40
    @11
    wph
    cS
    telgsums.s
    nn0red
    #
    adantr
    adantr
    @11
    @0
    cr
    wcel
    wph
    @22
    @0
    nn0re
    ad2antlr
    #
    @24
    @2
    @11
    @20
    wph
    @22
    @21
    ad2antlr
    nn0red
    @12
    @22
    simpr
    @24
    @0
    @42
    ltp1d
    lttrd
    ex
    @11
    @20
    @31
    @39
    @38
    wi
    #
    wph
    @21
    telgsums.u
    @20
    @31
    wa
    @30
    vk
    @2
    wsbc
    #
    @43
    @30
    vk
    @2
    cn0
    rspsbca
    @2
    cvv
    wcel
    #
    @44
    @43
    wb
    @0
    c1
    caddc
    ovex
    @45
    @44
    @28
    vk
    @2
    wsbc
    #
    @29
    vk
    @2
    wsbc
    #
    wi
    @43
    @28
    @29
    vk
    @2
    cvv
    sbcimg
    @45
    @46
    @39
    @47
    @38
    @45
    @46
    cS
    vk
    @2
    @27
    csb
    #
    clt
    wbr
    @39
    vk
    @2
    cS
    @27
    clt
    cvv
    sbcbr2g
    @45
    @48
    @2
    cS
    clt
    vk
    @2
    cvv
    csbvarg
    breq2d
    bitrd
    vk
    @2
    cC
    c.0
    cvv
    sbceq1g
    imbi12d
    bitrd
    ax-mp
    sylib
    syl2anr
    syld
    imp
    oveq12d
    @24
    @13
    c.0
    cB
    wcel
    #
    wa
    @25
    c.0
    wceq
    @24
    @13
    @49
    @12
    @13
    @22
    @17
    adantr
    cB
    cG
    c.0
    telgsums.b
    telgsums.0
    grpidcl
    jccir
    cB
    cG
    c.mi
    c.0
    c.0
    telgsums.b
    telgsums.0
    telgsums.m
    grpsubid
    syl
    eqtrd
    ex
    ralrimiva
    gsummptnn0fzv
    wph
    cB
    cC
    cS
    vi
    vk
    cG
    c.mi
    telgsums.b
    telgsums.g
    telgsums.m
    telgsums.s
    wph
    cc0
    @6
    cfz
    co
    #
    cn0
    wss
    @19
    @18
    vk
    @50
    wral
    wph
    @50
    cc0
    cuz
    cfv
    #
    cn0
    @50
    @51
    wss
    wph
    cc0
    @6
    fzssuz
    a1i
    nn0uz
    syl6sseqr
    telgsums.f
    @18
    vk
    @50
    cn0
    ssralv
    sylc
    telgsumfz0s
    wph
    @8
    @5
    c.0
    c.mi
    co
    #
    @5
    wph
    @7
    c.0
    @5
    c.mi
    wph
    @6
    cn0
    wcel
    #
    @31
    cS
    @6
    clt
    wbr
    #
    @7
    c.0
    wceq
    #
    wph
    cS
    cn0
    wcel
    @53
    telgsums.s
    cS
    peano2nn0
    syl
    telgsums.u
    wph
    cS
    @41
    ltp1d
    @53
    @31
    @54
    @55
    wi
    #
    @53
    @31
    wa
    @30
    vk
    @6
    wsbc
    #
    @56
    @30
    vk
    @6
    cn0
    rspsbca
    @6
    cvv
    wcel
    #
    @57
    @56
    wb
    cS
    c1
    caddc
    ovex
    @58
    @57
    @28
    vk
    @6
    wsbc
    #
    @29
    vk
    @6
    wsbc
    #
    wi
    @56
    @28
    @29
    vk
    @6
    cvv
    sbcimg
    @58
    @59
    @54
    @60
    @55
    @58
    @59
    cS
    vk
    @6
    @27
    csb
    #
    clt
    wbr
    @54
    vk
    @6
    cS
    @27
    clt
    cvv
    sbcbr2g
    @58
    @61
    @6
    cS
    clt
    vk
    @6
    cvv
    csbvarg
    breq2d
    bitrd
    vk
    @6
    cC
    c.0
    cvv
    sbceq1g
    imbi12d
    bitrd
    ax-mp
    sylib
    ex
    syl3c
    oveq2d
    wph
    @13
    @5
    cB
    wcel
    #
    @52
    @5
    wceq
    @16
    wph
    cc0
    cn0
    wcel
    #
    @19
    @62
    @63
    wph
    0nn0
    a1i
    telgsums.f
    vk
    cc0
    cn0
    cC
    cB
    rspcsbela
    syl2anc
    cB
    cG
    c.mi
    @5
    c.0
    telgsums.b
    telgsums.0
    telgsums.m
    grpsubid1
    syl2anc
    eqtrd
    3eqtrd
end
