include "co.mm"
include "wbr.mm"
include "csect.mm"
include "cfv.mm"
include "wa.mm"
include "crh.mm"
include "wcel.mm"
include "ccom.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "wceq.mm"
include "crs.mm"
include "ccnv.mm"
include "ccat.mm"
include "ringccatALTV.mm"
include "syl.mm"
include "eqid.mm"
include "isinv.mm"
include "w3a.mm"
include "ringcsectALTV.mm"
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
include "rhmf.mm"
include "anim12i.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "ad2antrl.mm"
include "jca.mm"
include "fcof1o.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "sylib.mm"
include "anass.mm"
include "sylanbrc.mm"
include "wb.mm"
include "isrim.mm"
include "anbi1d.mm"
include "adantr.mm"
include "mpbird.mm"
include "rimrhm.mm"
include "isrim0.mm"
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
include "rimf1o.mm"
include "f1ococnv1.mm"
include "eqtrd.mm"
include "jca31.mm"
include "wi.mm"
include "biimpcd.mm"
include "coeq2.mm"
include "f1ococnv2.mm"
include "impbida.mm"
include "3bitrd.mm"

theorem ringcinvALTV
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
  assume ringcsectALTV.c: |- C = ( RingCatALTV ` U )
  assume ringcsectALTV.b: |- B = ( Base ` C )
  assume ringcsectALTV.u: |- ( ph -> U e. V )
  assume ringcsectALTV.x: |- ( ph -> X e. B )
  assume ringcsectALTV.y: |- ( ph -> Y e. B )
  assume ringcinvALTV.n: |- N = ( Inv ` C )


  assert |- ( ph -> ( F ( X N Y ) G <-> ( F e. ( X RingIso Y ) /\ G = `' F ) ) )

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
    crh
    co
    wcel
    #
    cG
    cY
    cX
    crh
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
    crs
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
    ringcsectALTV.b
    ringcinvALTV.n
    wph
    cU
    cV
    wcel
    cC
    ccat
    wcel
    ringcsectALTV.u
    cC
    cU
    cV
    ringcsectALTV.c
    ringccatALTV
    syl
    ringcsectALTV.x
    ringcsectALTV.y
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
    ringcsectALTV.c
    ringcsectALTV.b
    ringcsectALTV.u
    ringcsectALTV.x
    ringcsectALTV.y
    @9
    eqid
    #
    @24
    ringcsectALTV
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
    ringcsectALTV.c
    ringcsectALTV.b
    ringcsectALTV.u
    ringcsectALTV.y
    ringcsectALTV.x
    @15
    eqid
    #
    @24
    ringcsectALTV
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
    #
    wa
    #
    @33
    @19
    @38
    wph
    @19
    @36
    @37
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
    rhmf
    @15
    @9
    cY
    cX
    cG
    @28
    @26
    rhmf
    anim12i
    ad2antlr
    @19
    @17
    @11
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
    jca
    jca
    adantl
    @38
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
    @39
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
    wa
    #
    @20
    @31
    wb
    wph
    @40
    @41
    ringcsectALTV.x
    ringcsectALTV.y
    jca
    #
    @9
    @15
    cX
    cY
    cF
    cB
    cB
    @26
    @28
    isrim
    syl
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
    @44
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
    rimrhm
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
    @45
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
    @42
    @20
    @47
    wb
    @43
    cX
    cY
    cF
    cB
    cB
    isrim0
    syl
    #
    @22
    @46
    @6
    @4
    @46
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
    @44
    @8
    @21
    cF
    ccom
    #
    @10
    @22
    @8
    @49
    wceq
    wph
    @20
    cG
    @21
    cF
    coeq1
    ad2antll
    @44
    @30
    @49
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
    rimf1o
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
    @44
    @7
    @47
    @23
    wph
    @47
    @20
    wph
    @47
    wi
    @22
    wph
    @20
    @47
    @48
    biimpcd
    adantr
    impcom
    @44
    @6
    @46
    @4
    @22
    @6
    @46
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
    @44
    @7
    @11
    @17
    @52
    @51
    @44
    @14
    cF
    @21
    ccom
    #
    @16
    @22
    @14
    @53
    wceq
    wph
    @20
    cG
    @21
    cF
    coeq2
    ad2antll
    @44
    @30
    @53
    @16
    wceq
    @50
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
