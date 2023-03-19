include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cima.mm"
include "ccnv.mm"
include "ctop.mm"
include "cntop1.mm"
include "adantr.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cuni.mm"
include "wf.mm"
include "wceq.mm"
include "eqid.mm"
include "cnf.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "cin.mm"
include "simpr.mm"
include "sseqtr4d.mm"
include "sseqin2.mm"
include "sylib.mm"
include "dminss.mm"
include "syl6eqssr.mm"
include "clsss.mm"
include "syl3anc.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "cncls2i.mm"
include "syldan.mm"
include "sstrd.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "clsss3.mm"
include "sylan.mm"
include "funimass3.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem cnclsi
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  assume cnclsi.1: |- X = U. J


  assert |- ( ( F e. ( J Cn K ) /\ S C_ X ) -> ( F " ( ( cls ` J ) ` S ) ) C_ ( ( cls ` K ) ` ( F " S ) ) )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cF
    cS
    cJ
    ccl
    cfv
    #
    cfv
    #
    cima
    cF
    cS
    cima
    #
    cK
    ccl
    cfv
    cfv
    #
    wss
    #
    @4
    cF
    ccnv
    #
    @6
    cima
    #
    wss
    #
    @2
    @4
    @8
    @5
    cima
    #
    @3
    cfv
    #
    @9
    @2
    cJ
    ctop
    wcel
    #
    @11
    cX
    wss
    cS
    @11
    wss
    @4
    @12
    wss
    @0
    @13
    @1
    cF
    cJ
    cK
    cntop1
    #
    adantr
    @2
    cF
    cdm
    #
    @11
    cX
    cF
    @5
    cnvimass
    @2
    cX
    cK
    cuni
    #
    cF
    wf
    #
    @15
    cX
    wceq
    @0
    @17
    @1
    cF
    cJ
    cK
    cX
    @16
    cnclsi.1
    @16
    eqid
    #
    cnf
    adantr
    #
    cX
    @16
    cF
    fdm
    syl
    #
    syl5sseq
    @2
    cS
    @15
    cS
    cin
    #
    @11
    @2
    cS
    @15
    wss
    @21
    cS
    wceq
    @2
    cS
    cX
    @15
    @0
    @1
    simpr
    @20
    sseqtr4d
    cS
    @15
    sseqin2
    sylib
    cS
    cF
    dminss
    syl6eqssr
    @11
    cS
    cJ
    cX
    cnclsi.1
    clsss
    syl3anc
    @0
    @1
    @5
    @16
    wss
    @12
    @9
    wss
    @2
    @5
    cF
    crn
    #
    @16
    cF
    cS
    imassrn
    @2
    @17
    @22
    @16
    wss
    @19
    cX
    @16
    cF
    frn
    syl
    syl5ss
    @5
    cF
    cJ
    cK
    @16
    @18
    cncls2i
    syldan
    sstrd
    @2
    cF
    wfun
    #
    @4
    @15
    wss
    @7
    @10
    wb
    @2
    @17
    @23
    @19
    cX
    @16
    cF
    ffun
    syl
    @2
    @4
    cX
    @15
    @0
    @13
    @1
    @4
    cX
    wss
    @14
    cS
    cJ
    cX
    cnclsi.1
    clsss3
    sylan
    @20
    sseqtr4d
    @4
    @6
    cF
    funimass3
    syl2anc
    mpbird
end
