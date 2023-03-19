include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wcel.mm"
include "wreu.mm"
include "wrex.mm"
include "chl.mm"
include "ccph.mm"
include "hlcph.mm"
include "syl.mm"
include "clss.mm"
include "syl6eleq.mm"
include "cress.mm"
include "ccms.mm"
include "ccld.mm"
include "wss.mm"
include "wb.mm"
include "hlcms.mm"
include "lssss.mm"
include "eqid.mm"
include "cmsss.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "minvec.mm"
include "reurex.mm"
include "wa.mm"
include "cabl.mm"
include "wceq.mm"
include "clmod.mm"
include "adantr.mm"
include "cphlmod.mm"
include "lmodabl.mm"
include "simprl.mm"
include "sseldd.mm"
include "ablpncan3.mm"
include "syl12anc.mm"
include "csubg.mm"
include "lsssssubg.mm"
include "cphl.mm"
include "cphphl.mm"
include "ocvlss.mm"
include "csca.mm"
include "c0g.mm"
include "lmodvsubcl.mm"
include "syl3anc.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "lssvacl.mm"
include "syl22anc.mm"
include "simplrr.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "sselda.mm"
include "grpsubsub4.mm"
include "syl13anc.mm"
include "breqtrrd.mm"
include "ralrimiva.mm"
include "pjthlem1.mm"
include "cclm.mm"
include "cphclm.mm"
include "clm0.mm"
include "eqtrd.mm"
include "elocv.mm"
include "syl3anbrc.mm"
include "lsmelvali.mm"
include "eqeltrrd.mm"
include "rexlimddv.mm"

theorem pjthlem2
  let wph: wff ph
  let cA: class A
  let c.pl: class .+
  let c.po: class .(+)
  let cU: class U
  let c.xi: class .,
  let cJ: class J
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cT: class T
  assume pjthlem.v: |- V = ( Base ` W )
  assume pjthlem.n: |- N = ( norm ` W )
  assume pjthlem.p: |- .+ = ( +g ` W )
  assume pjthlem.m: |- .- = ( -g ` W )
  assume pjthlem.h: |- ., = ( .i ` W )
  assume pjthlem.l: |- L = ( LSubSp ` W )
  assume pjthlem.1: |- ( ph -> W e. CHil )
  assume pjthlem.2: |- ( ph -> U e. L )
  assume pjthlem.4: |- ( ph -> A e. V )
  assume pjthlem.j: |- J = ( TopOpen ` W )
  assume pjthlem.s: |- .(+) = ( LSSum ` W )
  assume pjthlem.o: |- O = ( ocv ` W )
  assume pjthlem.3: |- ( ph -> U e. ( Clsd ` J ) )


  assert |- ( ph -> A e. ( U .(+) ( O ` U ) ) )

  proof
    wph
    cA
    vx
    cv
    #
    c.mi
    co
    #
    cN
    cfv
    #
    cA
    vy
    cv
    #
    c.mi
    co
    #
    cN
    cfv
    #
    cle
    wbr
    #
    vy
    cU
    wral
    #
    cA
    cU
    cU
    cO
    cfv
    #
    c.po
    co
    #
    wcel
    vx
    cU
    wph
    @7
    vx
    cU
    wreu
    @7
    vx
    cU
    wrex
    wph
    vx
    vy
    cA
    cW
    c.mi
    cN
    cV
    cU
    pjthlem.v
    pjthlem.m
    pjthlem.n
    wph
    cW
    chl
    wcel
    #
    cW
    ccph
    wcel
    #
    pjthlem.1
    cW
    hlcph
    syl
    #
    wph
    cU
    cL
    cW
    clss
    cfv
    pjthlem.2
    pjthlem.l
    syl6eleq
    wph
    cW
    cU
    cress
    co
    #
    ccms
    wcel
    #
    cU
    cJ
    ccld
    cfv
    wcel
    #
    pjthlem.3
    wph
    cW
    ccms
    wcel
    #
    cU
    cV
    wss
    #
    @14
    @15
    wb
    wph
    @10
    @16
    pjthlem.1
    cW
    hlcms
    syl
    wph
    cU
    cL
    wcel
    #
    @17
    pjthlem.2
    cL
    cU
    cV
    cW
    pjthlem.v
    pjthlem.l
    lssss
    #
    syl
    cU
    cJ
    @13
    cW
    cV
    @13
    eqid
    pjthlem.v
    pjthlem.j
    cmsss
    syl2anc
    mpbird
    pjthlem.4
    minvec
    @7
    vx
    cU
    reurex
    syl
    wph
    @0
    cU
    wcel
    #
    @7
    wa
    #
    wa
    #
    @0
    @1
    c.pl
    co
    #
    cA
    @9
    @22
    cW
    cabl
    wcel
    #
    @0
    cV
    wcel
    #
    cA
    cV
    wcel
    #
    @23
    cA
    wceq
    @22
    cW
    clmod
    wcel
    #
    @24
    @22
    @11
    @27
    wph
    @11
    @21
    @12
    adantr
    #
    cW
    cphlmod
    syl
    #
    cW
    lmodabl
    syl
    @22
    cU
    cV
    @0
    @22
    @18
    @17
    wph
    @18
    @21
    pjthlem.2
    adantr
    #
    @19
    syl
    #
    wph
    @20
    @7
    simprl
    #
    sseldd
    #
    wph
    @26
    @21
    pjthlem.4
    adantr
    #
    cV
    c.pl
    cW
    c.mi
    @0
    cA
    pjthlem.v
    pjthlem.p
    pjthlem.m
    ablpncan3
    syl12anc
    @22
    cU
    cW
    csubg
    cfv
    #
    wcel
    @8
    @35
    wcel
    @20
    @1
    @8
    wcel
    #
    @23
    @9
    wcel
    @22
    cL
    @35
    cU
    @22
    @27
    cL
    @35
    wss
    @29
    cL
    cW
    pjthlem.l
    lsssssubg
    syl
    #
    @30
    sseldd
    @22
    cL
    @35
    @8
    @37
    @22
    cW
    cphl
    wcel
    #
    @17
    @8
    cL
    wcel
    @22
    @11
    @38
    @28
    cW
    cphphl
    syl
    @31
    cU
    cL
    cO
    cV
    cW
    pjthlem.v
    pjthlem.o
    pjthlem.l
    ocvlss
    syl2anc
    sseldd
    @32
    @22
    @17
    @1
    cV
    wcel
    #
    @1
    vz
    cv
    #
    c.xi
    co
    #
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    vz
    cU
    wral
    @36
    @31
    @22
    @27
    @26
    @25
    @39
    @29
    @34
    @33
    c.mi
    cV
    cW
    cA
    @0
    pjthlem.v
    pjthlem.m
    lmodvsubcl
    syl3anc
    #
    @22
    @44
    vz
    cU
    @22
    @40
    cU
    wcel
    #
    wa
    #
    @41
    cc0
    @43
    @47
    vw
    @1
    @40
    c.pl
    @41
    @40
    @40
    c.xi
    co
    c1
    caddc
    co
    cdiv
    co
    #
    cU
    c.xi
    cL
    c.mi
    cN
    cV
    cW
    pjthlem.v
    pjthlem.n
    pjthlem.p
    pjthlem.m
    pjthlem.h
    pjthlem.l
    wph
    @10
    @21
    @46
    pjthlem.1
    ad2antrr
    @22
    @18
    @46
    @30
    adantr
    @22
    @39
    @46
    @45
    adantr
    @22
    @46
    simpr
    @22
    @2
    @1
    vw
    cv
    #
    c.mi
    co
    #
    cN
    cfv
    #
    cle
    wbr
    #
    vw
    cU
    wral
    @46
    @22
    @52
    vw
    cU
    @22
    @49
    cU
    wcel
    #
    wa
    #
    @2
    cA
    @49
    @0
    c.pl
    co
    #
    c.mi
    co
    #
    cN
    cfv
    #
    @51
    cle
    @54
    @55
    cU
    wcel
    #
    @7
    @2
    @57
    cle
    wbr
    #
    @54
    @27
    @18
    @53
    @20
    @58
    @22
    @27
    @53
    @29
    adantr
    @22
    @18
    @53
    @30
    adantr
    @22
    @53
    simpr
    @22
    @20
    @53
    @32
    adantr
    c.pl
    cL
    cU
    cW
    @49
    @0
    pjthlem.p
    pjthlem.l
    lssvacl
    syl22anc
    wph
    @20
    @7
    @53
    simplrr
    @6
    @59
    vy
    @55
    cU
    @3
    @55
    wceq
    #
    @5
    @57
    @2
    cle
    @60
    @4
    @56
    cN
    @3
    @55
    cA
    c.mi
    oveq2
    fveq2d
    breq2d
    rspcv
    sylc
    @54
    @50
    @56
    cN
    @54
    cW
    cgrp
    wcel
    #
    @26
    @25
    @49
    cV
    wcel
    @50
    @56
    wceq
    @22
    @61
    @53
    @22
    @27
    @61
    @29
    cW
    lmodgrp
    syl
    adantr
    @22
    @26
    @53
    @34
    adantr
    @22
    @25
    @53
    @33
    adantr
    @22
    cU
    cV
    @49
    @31
    sselda
    cV
    c.pl
    cW
    c.mi
    cA
    @0
    @49
    pjthlem.v
    pjthlem.p
    pjthlem.m
    grpsubsub4
    syl13anc
    fveq2d
    breqtrrd
    ralrimiva
    adantr
    @48
    eqid
    pjthlem1
    @47
    cW
    cclm
    wcel
    #
    cc0
    @43
    wceq
    @47
    @11
    @62
    @22
    @11
    @46
    @28
    adantr
    cW
    cphclm
    syl
    @42
    cW
    @42
    eqid
    #
    clm0
    syl
    eqtrd
    ralrimiva
    vz
    @1
    cU
    @42
    c.xi
    cO
    cV
    cW
    @43
    pjthlem.v
    pjthlem.h
    @63
    @43
    eqid
    pjthlem.o
    elocv
    syl3anbrc
    c.pl
    c.po
    cU
    @8
    cW
    @0
    @1
    pjthlem.p
    pjthlem.s
    lsmelvali
    syl22anc
    eqeltrrd
    rexlimddv
end
