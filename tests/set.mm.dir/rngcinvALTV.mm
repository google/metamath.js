include "co.mm"
include "wbr.mm"
include "csect.mm"
include "cfv.mm"
include "wa.mm"
include "crngh.mm"
include "wcel.mm"
include "ccom.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "wceq.mm"
include "crngs.mm"
include "ccnv.mm"
include "ccat.mm"
include "rngccatALTV.mm"
include "syl.mm"
include "eqid.mm"
include "isinv.mm"
include "w3a.mm"
include "rngcsectALTV.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "3ancoma.mm"
include "bitri.mm"
include "anbi12d.mm"
include "anandi.mm"
include "wf1o.mm"
include "simplrl.mm"
include "adantl.mm"
include "wf.mm"
include "rnghmf.mm"
include "anim12i.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "ad2antrl.mm"
include "jca32.mm"
include "fcof1o.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "sylib.mm"
include "anass.mm"
include "sylanbrc.mm"
include "wb.mm"
include "isrngim.mm"
include "syl2anc.mm"
include "anbi1d.mm"
include "adantr.mm"
include "mpbird.mm"
include "rngimrnghm.mm"
include "isrngisom.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "anbi2d.mm"
include "sylan9bbr.mm"
include "syl6bi.mm"
include "com12.mm"
include "expdimp.mm"
include "impcom.mm"
include "coeq1.mm"
include "ad2antll.mm"
include "rngimf1o.mm"
include "f1ococnv1.mm"
include "eqtrd.mm"
include "jca31.mm"
include "wi.mm"
include "biimpcd.mm"
include "coeq2.mm"
include "f1ococnv2.mm"
include "impbida.mm"
include "3bitrd.mm"

theorem rngcinvALTV
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume rngcsectALTV.c: |- C = ( RngCatALTV ` U )
  assume rngcsectALTV.b: |- B = ( Base ` C )
  assume rngcsectALTV.u: |- ( ph -> U e. V )
  assume rngcsectALTV.x: |- ( ph -> X e. B )
  assume rngcsectALTV.y: |- ( ph -> Y e. B )
  assume rngcinvALTV.n: |- N = ( Inv ` C )


  assert |- ( ph -> ( F ( X N Y ) G <-> ( F e. ( X RngIsom Y ) /\ G = `' F ) ) )

  proof
    wph
    cF
    cG
    cX
    cY
    cN
    co
    wbr
    cF
    cG
    cX
    cY
    cC
    csect
    cfv
    #
    co
    wbr
    #
    cG
    cF
    cY
    cX
    @0
    co
    wbr
    #
    wa
    #
    cF
    cX
    cY
    crngh
    co
    wcel
    #
    cG
    cY
    cX
    crngh
    co
    #
    wcel
    #
    wa
    #
    cG
    cF
    ccom
    #
    cid
    cX
    cbs
    cfv
    #
    cres
    #
    wceq
    #
    wa
    #
    @7
    wa
    #
    @12
    cF
    cG
    ccom
    #
    cid
    cY
    cbs
    cfv
    #
    cres
    #
    wceq
    #
    wa
    #
    wa
    #
    cF
    cX
    cY
    crngs
    co
    wcel
    #
    cG
    cF
    ccnv
    #
    wceq
    #
    wa
    #
    wph
    cB
    cC
    @0
    cF
    cG
    cN
    cX
    cY
    rngcsectALTV.b
    rngcinvALTV.n
    wph
    cU
    cV
    wcel
    cC
    ccat
    wcel
    rngcsectALTV.u
    cC
    cU
    cV
    rngcsectALTV.c
    rngccatALTV
    syl
    rngcsectALTV.x
    rngcsectALTV.y
    @0
    eqid
    #
    isinv
    wph
    @3
    @12
    @7
    @17
    wa
    #
    wa
    @19
    wph
    @1
    @12
    @2
    @25
    wph
    @1
    @4
    @6
    @11
    w3a
    @12
    wph
    cB
    cC
    @0
    cU
    @9
    cF
    cG
    cV
    cX
    cY
    rngcsectALTV.c
    rngcsectALTV.b
    rngcsectALTV.u
    rngcsectALTV.x
    rngcsectALTV.y
    @9
    eqid
    #
    @24
    rngcsectALTV
    @4
    @6
    @11
    df-3an
    syl6bb
    wph
    @2
    @6
    @4
    @17
    w3a
    #
    @25
    wph
    cB
    cC
    @0
    cU
    @15
    cG
    cF
    cV
    cY
    cX
    rngcsectALTV.c
    rngcsectALTV.b
    rngcsectALTV.u
    rngcsectALTV.y
    rngcsectALTV.x
    @15
    eqid
    #
    @24
    rngcsectALTV
    @27
    @4
    @6
    @17
    w3a
    @25
    @6
    @4
    @17
    3ancoma
    @4
    @6
    @17
    df-3an
    bitri
    syl6bb
    anbi12d
    @12
    @7
    @17
    anandi
    syl6bb
    wph
    @19
    @23
    wph
    @19
    wa
    #
    @23
    @4
    @9
    @15
    cF
    wf1o
    #
    wa
    #
    @22
    wa
    #
    @29
    @4
    @30
    @22
    wa
    #
    @32
    @19
    @4
    wph
    @12
    @4
    @6
    @18
    simplrl
    adantl
    @29
    @9
    @15
    cF
    wf
    #
    @15
    @9
    cG
    wf
    #
    wa
    #
    @17
    @11
    wa
    wa
    #
    @33
    @19
    @37
    wph
    @19
    @36
    @17
    @11
    @7
    @36
    @12
    @18
    @4
    @34
    @6
    @35
    @9
    @15
    cX
    cY
    cF
    @26
    @28
    rnghmf
    @15
    @9
    cY
    cX
    cG
    @28
    @26
    rnghmf
    anim12i
    ad2antlr
    @18
    @17
    @13
    @12
    @17
    simpr
    adantl
    @12
    @11
    @13
    @17
    @7
    @11
    simpr
    ad2antrl
    jca32
    adantl
    @37
    @30
    @21
    cG
    wceq
    #
    wa
    @33
    @9
    @15
    cF
    cG
    fcof1o
    @38
    @22
    @30
    @21
    cG
    eqcom
    anbi2i
    sylib
    syl
    @4
    @30
    @22
    anass
    sylanbrc
    wph
    @23
    @32
    wb
    @19
    wph
    @20
    @31
    @22
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @20
    @31
    wb
    rngcsectALTV.x
    rngcsectALTV.y
    @9
    @15
    cX
    cY
    cF
    cB
    cB
    @26
    @28
    isrngim
    syl2anc
    anbi1d
    adantr
    mpbird
    wph
    @23
    wa
    #
    @12
    @7
    @18
    @41
    @4
    @6
    @11
    @20
    @4
    wph
    @22
    @9
    @15
    cX
    cY
    cF
    @26
    @28
    rngimrnghm
    ad2antrl
    @23
    wph
    @6
    @20
    @22
    wph
    @6
    @22
    wph
    wa
    #
    @20
    @6
    @42
    @20
    @7
    @6
    wph
    @20
    @4
    @21
    @5
    wcel
    #
    wa
    #
    @22
    @7
    wph
    @39
    @40
    @20
    @44
    wb
    rngcsectALTV.x
    rngcsectALTV.y
    cX
    cY
    cF
    cB
    cB
    isrngisom
    syl2anc
    #
    @22
    @43
    @6
    @4
    @43
    @6
    wb
    @21
    cG
    @21
    cG
    @5
    eleq1
    eqcoms
    anbi2d
    sylan9bbr
    @4
    @6
    simpr
    syl6bi
    com12
    expdimp
    impcom
    @41
    @8
    @21
    cF
    ccom
    #
    @10
    @22
    @8
    @46
    wceq
    wph
    @20
    cG
    @21
    cF
    coeq1
    ad2antll
    @41
    @30
    @46
    @10
    wceq
    @20
    @30
    wph
    @22
    @9
    @15
    cX
    cY
    cF
    @26
    @28
    rngimf1o
    ad2antrl
    #
    @9
    @15
    cF
    f1ococnv1
    syl
    eqtrd
    #
    jca31
    @41
    @7
    @44
    @23
    wph
    @44
    @20
    wph
    @44
    wi
    @22
    wph
    @20
    @44
    @45
    biimpcd
    adantr
    impcom
    @41
    @6
    @43
    @4
    @22
    @6
    @43
    wb
    wph
    @20
    cG
    @21
    @5
    eleq1
    ad2antll
    anbi2d
    mpbird
    #
    @41
    @7
    @11
    @17
    @49
    @48
    @41
    @14
    cF
    @21
    ccom
    #
    @16
    @22
    @14
    @50
    wceq
    wph
    @20
    cG
    @21
    cF
    coeq2
    ad2antll
    @41
    @30
    @50
    @16
    wceq
    @47
    @9
    @15
    cF
    f1ococnv2
    syl
    eqtrd
    jca31
    jca31
    impbida
    3bitrd
end
