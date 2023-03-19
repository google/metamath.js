include "cima.mm"
include "ctcl.mm"
include "cfv.mm"
include "ccnv.mm"
include "ccom.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "trclfvlb.mm"
include "imass1.mm"
include "3syl.mm"
include "ssun2.mm"
include "sstri.mm"
include "syl6ss.mm"
include "cid.mm"
include "crn.mm"
include "cres.mm"
include "wceq.mm"
include "trclfvdecomr.mm"
include "syl.mm"
include "cnveqd.mm"
include "cnvun.mm"
include "cnvco.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "coeq2d.mm"
include "coundi.mm"
include "wfun.mm"
include "funcocnv2.mm"
include "coass.mm"
include "eqcomi.mm"
include "coeq1d.mm"
include "syl5eq.mm"
include "uneq12d.mm"
include "eqtrd.mm"
include "imaeq1d.mm"
include "imaundir.mm"
include "resss.mm"
include "ax-mp.mm"
include "imai.mm"
include "sseqtri.mm"
include "imaco.mm"
include "eqsstri.mm"
include "unss12.mm"
include "mp2an.mm"
include "ssun1.mm"
include "unass.mm"
include "syl6eqss.mm"
include "coss1.mm"
include "trclfvcotrg.mm"
include "unssd.mm"
include "imaeq2d.mm"
include "imaundi.mm"
include "uneq12i.mm"
include "3sstr4d.mm"

theorem frege131d
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cF: class F
  assume frege131d.f: |- ( ph -> F e. _V )
  assume frege131d.a: |- ( ph -> A = ( U u. ( ( `' ( t+ ` F ) " U ) u. ( ( t+ ` F ) " U ) ) ) )
  assume frege131d.fun: |- ( ph -> Fun F )


  assert |- ( ph -> ( F " A ) C_ A )

  proof
    wph
    cF
    cU
    cima
    #
    cF
    cF
    ctcl
    cfv
    #
    ccnv
    #
    ccom
    #
    cU
    cima
    #
    cF
    @1
    ccom
    #
    cU
    cima
    #
    cun
    #
    cun
    #
    cU
    @2
    cU
    cima
    #
    @1
    cU
    cima
    #
    cun
    #
    cun
    #
    cF
    cA
    cima
    #
    cA
    wph
    @0
    @7
    @12
    wph
    @0
    @10
    @12
    wph
    cF
    cvv
    wcel
    #
    cF
    @1
    wss
    #
    @0
    @10
    wss
    frege131d.f
    cF
    cvv
    trclfvlb
    #
    cF
    @1
    cU
    imass1
    3syl
    @10
    @11
    @12
    @10
    @9
    ssun2
    @11
    cU
    ssun2
    sstri
    #
    syl6ss
    wph
    @4
    @6
    @12
    wph
    @4
    cid
    cF
    crn
    #
    cres
    #
    cU
    cima
    #
    @19
    @2
    ccom
    #
    cU
    cima
    #
    cun
    #
    @12
    wph
    @4
    @19
    @21
    cun
    #
    cU
    cima
    @23
    wph
    @3
    @24
    cU
    wph
    @3
    cF
    cF
    ccnv
    #
    @25
    @2
    ccom
    #
    cun
    #
    ccom
    #
    @24
    wph
    @2
    @27
    cF
    wph
    @2
    cF
    @1
    cF
    ccom
    #
    cun
    #
    ccnv
    #
    @27
    wph
    @1
    @30
    wph
    @14
    @1
    @30
    wceq
    frege131d.f
    cF
    cvv
    trclfvdecomr
    syl
    cnveqd
    @31
    @25
    @29
    ccnv
    #
    cun
    @27
    cF
    @29
    cnvun
    @32
    @26
    @25
    @1
    cF
    cnvco
    uneq2i
    eqtri
    syl6eq
    coeq2d
    wph
    @28
    cF
    @25
    ccom
    #
    cF
    @26
    ccom
    #
    cun
    @24
    cF
    @25
    @26
    coundi
    wph
    @33
    @19
    @34
    @21
    wph
    cF
    wfun
    @33
    @19
    wceq
    frege131d.fun
    cF
    funcocnv2
    syl
    #
    wph
    @34
    @33
    @2
    ccom
    #
    @21
    @36
    @34
    cF
    @25
    @2
    coass
    eqcomi
    wph
    @33
    @19
    @2
    @35
    coeq1d
    syl5eq
    uneq12d
    syl5eq
    eqtrd
    imaeq1d
    @19
    @21
    cU
    imaundir
    syl6eq
    @23
    cU
    @9
    cun
    #
    @12
    @20
    cU
    wss
    @22
    @9
    wss
    @23
    @37
    wss
    @20
    cid
    cU
    cima
    #
    cU
    @19
    cid
    wss
    #
    @20
    @38
    wss
    cid
    @18
    resss
    #
    @19
    cid
    cU
    imass1
    ax-mp
    cU
    imai
    sseqtri
    @22
    @19
    @9
    cima
    #
    @9
    @19
    @2
    cU
    imaco
    @41
    cid
    @9
    cima
    #
    @9
    @39
    @41
    @42
    wss
    @40
    @19
    cid
    @9
    imass1
    ax-mp
    @9
    imai
    sseqtri
    eqsstri
    @20
    cU
    @22
    @9
    unss12
    mp2an
    @37
    @37
    @10
    cun
    @12
    @37
    @10
    ssun1
    cU
    @9
    @10
    unass
    sseqtri
    sstri
    syl6eqss
    wph
    @6
    @10
    @12
    wph
    @5
    @1
    wss
    @6
    @10
    wss
    wph
    @5
    @1
    @1
    ccom
    #
    @1
    wph
    @14
    @15
    @5
    @43
    wss
    frege131d.f
    @16
    cF
    @1
    @1
    coss1
    3syl
    cF
    trclfvcotrg
    syl6ss
    @5
    @1
    cU
    imass1
    syl
    @17
    syl6ss
    unssd
    unssd
    wph
    @13
    cF
    @12
    cima
    #
    @8
    wph
    cA
    @12
    cF
    frege131d.a
    imaeq2d
    @44
    @0
    cF
    @11
    cima
    #
    cun
    @8
    cF
    cU
    @11
    imaundi
    @45
    @7
    @0
    @45
    cF
    @9
    cima
    #
    cF
    @10
    cima
    #
    cun
    @7
    cF
    @9
    @10
    imaundi
    @46
    @4
    @47
    @6
    @4
    @46
    cF
    @2
    cU
    imaco
    eqcomi
    @6
    @47
    cF
    @1
    cU
    imaco
    eqcomi
    uneq12i
    eqtri
    uneq2i
    eqtri
    syl6eq
    frege131d.a
    3sstr4d
end
