include "co.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "cmpt.mm"
include "clt.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cplusg.mm"
include "cof.mm"
include "eqid.mm"
include "mpladd.mm"
include "fveq1d.mm"
include "adantr.mm"
include "wfn.mm"
include "cvv.mm"
include "cbs.mm"
include "wf.mm"
include "mplelf.mm"
include "ffn.mm"
include "syl.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "simpr.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "adantrr.mm"
include "simprl.mm"
include "cxr.mm"
include "w3a.mm"
include "mdegxrcl.mm"
include "ifcld.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "tdeglem1.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "3jca.mm"
include "xrmax1.mm"
include "syl2anc.mm"
include "simprr.mm"
include "jca.mm"
include "xrlelttr.mm"
include "sylc.mm"
include "mdeglt.mm"
include "xrmax2.mm"
include "oveq12d.mm"
include "cgrp.mm"
include "crg.mm"
include "ringgrp.mm"
include "ring0cl.mm"
include "grplid.mm"
include "expr.mm"
include "ralrimiva.mm"
include "wb.mm"
include "mplring.mm"
include "ringacl.mm"
include "syl3anc.mm"
include "mdegleb.mm"
include "mpbird.mm"

theorem mdegaddle
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cY: class Y
  let vc: setvar c
  let va: setvar a
  let vb: setvar b
  assume mdegaddle.y: |- Y = ( I mPoly R )
  assume mdegaddle.d: |- D = ( I mDeg R )
  assume mdegaddle.i: |- ( ph -> I e. V )
  assume mdegaddle.r: |- ( ph -> R e. Ring )
  assume mdegaddle.b: |- B = ( Base ` Y )
  assume mdegaddle.p: |- .+ = ( +g ` Y )
  assume mdegaddle.f: |- ( ph -> F e. B )
  assume mdegaddle.g: |- ( ph -> G e. B )


  assert |- ( ph -> ( D ` ( F .+ G ) ) <_ if ( ( D ` F ) <_ ( D ` G ) , ( D ` G ) , ( D ` F ) ) )

  proof
    wph
    cF
    cG
    c.pl
    co
    #
    cD
    cfv
    cF
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    cle
    wbr
    #
    @2
    @1
    cif
    #
    cle
    wbr
    #
    @4
    vc
    cv
    #
    vb
    va
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    va
    cn0
    cI
    cmap
    co
    #
    crab
    #
    ccnfld
    vb
    cv
    cgsu
    co
    cmpt
    #
    cfv
    #
    clt
    wbr
    #
    @6
    @0
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vc
    @9
    wral
    #
    wph
    @16
    vc
    @9
    wph
    @6
    @9
    wcel
    #
    @12
    @15
    wph
    @18
    @12
    wa
    #
    wa
    #
    @13
    @6
    cF
    cfv
    #
    @6
    cG
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    @14
    wph
    @18
    @13
    @24
    wceq
    @12
    wph
    @18
    wa
    #
    @13
    @6
    cF
    cG
    @23
    cof
    co
    #
    cfv
    #
    @24
    wph
    @13
    @27
    wceq
    @18
    wph
    @6
    @0
    @26
    wph
    cB
    cY
    @23
    c.pl
    cR
    cI
    cF
    cG
    mdegaddle.y
    mdegaddle.b
    @23
    eqid
    #
    mdegaddle.p
    mdegaddle.f
    mdegaddle.g
    mpladd
    fveq1d
    adantr
    @25
    cF
    @9
    wfn
    #
    cG
    @9
    wfn
    #
    @9
    cvv
    wcel
    #
    @18
    @27
    @24
    wceq
    wph
    @29
    @18
    wph
    @9
    cR
    cbs
    cfv
    #
    cF
    wf
    @29
    wph
    cB
    @9
    cY
    cR
    va
    cI
    @32
    cF
    mdegaddle.y
    @32
    eqid
    #
    mdegaddle.b
    @9
    eqid
    #
    mdegaddle.f
    mplelf
    @9
    @32
    cF
    ffn
    syl
    adantr
    wph
    @30
    @18
    wph
    @9
    @32
    cG
    wf
    @30
    wph
    cB
    @9
    cY
    cR
    va
    cI
    @32
    cG
    mdegaddle.y
    @33
    mdegaddle.b
    @34
    mdegaddle.g
    mplelf
    @9
    @32
    cG
    ffn
    syl
    adantr
    @31
    @25
    @7
    va
    @8
    cn0
    cI
    cmap
    ovex
    rabex
    a1i
    wph
    @18
    simpr
    @9
    @23
    cF
    cG
    cvv
    @6
    fnfvof
    syl22anc
    eqtrd
    adantrr
    @20
    @24
    @14
    @14
    @23
    co
    #
    @14
    @20
    @21
    @14
    @22
    @14
    @23
    @20
    @9
    cB
    cD
    cY
    cR
    vb
    va
    cF
    @10
    cI
    @6
    @14
    mdegaddle.d
    mdegaddle.y
    mdegaddle.b
    @14
    eqid
    #
    @34
    @10
    eqid
    #
    wph
    cF
    cB
    wcel
    #
    @19
    mdegaddle.f
    adantr
    wph
    @18
    @12
    simprl
    #
    @20
    @1
    cxr
    wcel
    #
    @4
    cxr
    wcel
    #
    @11
    cxr
    wcel
    #
    w3a
    #
    @1
    @4
    cle
    wbr
    #
    @12
    wa
    @1
    @11
    clt
    wbr
    wph
    @18
    @43
    @12
    @25
    @40
    @41
    @42
    wph
    @40
    @18
    wph
    @38
    @40
    mdegaddle.f
    cB
    cD
    cY
    cR
    cF
    cI
    mdegaddle.d
    mdegaddle.y
    mdegaddle.b
    mdegxrcl
    syl
    #
    adantr
    wph
    @41
    @18
    wph
    @3
    @2
    @1
    cxr
    wph
    cG
    cB
    wcel
    #
    @2
    cxr
    wcel
    #
    mdegaddle.g
    cB
    cD
    cY
    cR
    cG
    cI
    mdegaddle.d
    mdegaddle.y
    mdegaddle.b
    mdegxrcl
    syl
    #
    @45
    ifcld
    #
    adantr
    #
    @25
    cn0
    cxr
    @11
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    wph
    @9
    cn0
    @6
    @10
    wph
    cI
    cV
    wcel
    #
    @9
    cn0
    @10
    wf
    mdegaddle.i
    @9
    vb
    va
    @10
    cI
    cV
    @34
    @37
    tdeglem1
    syl
    ffvelrnda
    sseldi
    #
    3jca
    adantrr
    @20
    @44
    @12
    wph
    @44
    @19
    wph
    @40
    @47
    @44
    @45
    @48
    @1
    @2
    xrmax1
    syl2anc
    adantr
    wph
    @18
    @12
    simprr
    #
    jca
    @1
    @4
    @11
    xrlelttr
    sylc
    mdeglt
    @20
    @9
    cB
    cD
    cY
    cR
    vb
    va
    cG
    @10
    cI
    @6
    @14
    mdegaddle.d
    mdegaddle.y
    mdegaddle.b
    @36
    @34
    @37
    wph
    @46
    @19
    mdegaddle.g
    adantr
    @39
    @20
    @47
    @41
    @42
    w3a
    #
    @2
    @4
    cle
    wbr
    #
    @12
    wa
    @2
    @11
    clt
    wbr
    wph
    @18
    @54
    @12
    @25
    @47
    @41
    @42
    wph
    @47
    @18
    @48
    adantr
    @50
    @52
    3jca
    adantrr
    @20
    @55
    @12
    wph
    @55
    @19
    wph
    @40
    @47
    @55
    @45
    @48
    @1
    @2
    xrmax2
    syl2anc
    adantr
    @53
    jca
    @2
    @4
    @11
    xrlelttr
    sylc
    mdeglt
    oveq12d
    wph
    @35
    @14
    wceq
    #
    @19
    wph
    cR
    cgrp
    wcel
    #
    @14
    @32
    wcel
    #
    @56
    wph
    cR
    crg
    wcel
    #
    @57
    mdegaddle.r
    cR
    ringgrp
    syl
    wph
    @59
    @58
    mdegaddle.r
    @32
    cR
    @14
    @33
    @36
    ring0cl
    syl
    @32
    @23
    cR
    @14
    @14
    @33
    @28
    @36
    grplid
    syl2anc
    adantr
    eqtrd
    eqtrd
    expr
    ralrimiva
    wph
    @0
    cB
    wcel
    #
    @41
    @5
    @17
    wb
    wph
    cY
    crg
    wcel
    #
    @38
    @46
    @60
    wph
    @51
    @59
    @61
    mdegaddle.i
    mdegaddle.r
    cY
    cR
    cI
    cV
    mdegaddle.y
    mplring
    syl2anc
    mdegaddle.f
    mdegaddle.g
    cB
    c.pl
    cY
    cF
    cG
    mdegaddle.b
    mdegaddle.p
    ringacl
    syl3anc
    @49
    vc
    @9
    cB
    cD
    cY
    cR
    vb
    va
    @0
    @4
    @10
    cI
    @14
    mdegaddle.d
    mdegaddle.y
    mdegaddle.b
    @36
    @34
    @37
    mdegleb
    syl2anc
    mpbird
end
