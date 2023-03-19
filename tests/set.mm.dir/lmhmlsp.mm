include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cima.mm"
include "wfun.mm"
include "ccnv.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "lmhmf.mm"
include "adantr.mm"
include "ffun.mm"
include "syl.mm"
include "clmod.mm"
include "clss.mm"
include "lmhmlmod1.mm"
include "lmhmlmod2.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "lspcl.mm"
include "syl2anc.mm"
include "lmhmpreima.mm"
include "syldan.mm"
include "cdm.mm"
include "cin.mm"
include "incom.mm"
include "wceq.mm"
include "simpr.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5req.mm"
include "dminss.mm"
include "syl6eqss.mm"
include "lspssid.mm"
include "imass2.mm"
include "sstrd.mm"
include "lspssp.mm"
include "syl3anc.mm"
include "funimass2.mm"
include "lmhmima.mm"
include "eqssd.mm"

theorem lmhmlsp
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cK: class K
  let cL: class L
  let cV: class V
  assume lmhmlsp.v: |- V = ( Base ` S )
  assume lmhmlsp.k: |- K = ( LSpan ` S )
  assume lmhmlsp.l: |- L = ( LSpan ` T )


  assert |- ( ( F e. ( S LMHom T ) /\ U C_ V ) -> ( F " ( K ` U ) ) = ( L ` ( F " U ) ) )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cU
    cV
    wss
    #
    wa
    #
    cF
    cU
    cK
    cfv
    #
    cima
    #
    cF
    cU
    cima
    #
    cL
    cfv
    #
    @2
    cF
    wfun
    #
    @3
    cF
    ccnv
    #
    @6
    cima
    #
    wss
    #
    @4
    @6
    wss
    @2
    cV
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @7
    @0
    @12
    @1
    cV
    @11
    cS
    cT
    cF
    lmhmlsp.v
    @11
    eqid
    #
    lmhmf
    adantr
    #
    cV
    @11
    cF
    ffun
    syl
    @2
    cS
    clmod
    wcel
    #
    @9
    cS
    clss
    cfv
    #
    wcel
    #
    cU
    @9
    wss
    @10
    @0
    @15
    @1
    cS
    cT
    cF
    lmhmlmod1
    adantr
    #
    @0
    @1
    @6
    cT
    clss
    cfv
    #
    wcel
    #
    @17
    @2
    cT
    clmod
    wcel
    #
    @5
    @11
    wss
    #
    @20
    @0
    @21
    @1
    cS
    cT
    cF
    lmhmlmod2
    adantr
    #
    @2
    @5
    cF
    crn
    #
    @11
    cF
    cU
    imassrn
    @2
    @12
    @24
    @11
    wss
    @14
    cV
    @11
    cF
    frn
    syl
    syl5ss
    #
    @19
    @5
    cL
    @11
    cT
    @13
    @19
    eqid
    #
    lmhmlsp.l
    lspcl
    syl2anc
    cS
    cT
    @6
    cF
    @16
    @19
    @16
    eqid
    #
    @26
    lmhmpreima
    syldan
    @2
    cU
    @8
    @5
    cima
    #
    @9
    @2
    cU
    cF
    cdm
    #
    cU
    cin
    #
    @28
    @2
    @30
    cU
    @29
    cin
    #
    cU
    @29
    cU
    incom
    @2
    cU
    @29
    wss
    @31
    cU
    wceq
    @2
    cU
    cV
    @29
    @0
    @1
    simpr
    #
    @2
    @12
    @29
    cV
    wceq
    @14
    cV
    @11
    cF
    fdm
    syl
    sseqtr4d
    cU
    @29
    df-ss
    sylib
    syl5req
    cU
    cF
    dminss
    syl6eqss
    @2
    @5
    @6
    wss
    #
    @28
    @9
    wss
    @2
    @21
    @22
    @33
    @23
    @25
    @5
    cL
    @11
    cT
    @13
    lmhmlsp.l
    lspssid
    syl2anc
    @5
    @6
    @8
    imass2
    syl
    sstrd
    @16
    cU
    @9
    cK
    cS
    @27
    lmhmlsp.k
    lspssp
    syl3anc
    @3
    @6
    cF
    funimass2
    syl2anc
    @2
    @21
    @4
    @19
    wcel
    #
    @5
    @4
    wss
    #
    @6
    @4
    wss
    @23
    @0
    @1
    @3
    @16
    wcel
    #
    @34
    @2
    @15
    @1
    @36
    @18
    @32
    @16
    cU
    cK
    cV
    cS
    lmhmlsp.v
    @27
    lmhmlsp.k
    lspcl
    syl2anc
    cS
    cT
    @3
    cF
    @16
    @19
    @27
    @26
    lmhmima
    syldan
    @2
    cU
    @3
    wss
    #
    @35
    @2
    @15
    @1
    @37
    @18
    @32
    cU
    cK
    cV
    cS
    lmhmlsp.v
    lmhmlsp.k
    lspssid
    syl2anc
    cU
    @3
    cF
    imass2
    syl
    @19
    @5
    @4
    cL
    cT
    @26
    lmhmlsp.l
    lspssp
    syl3anc
    eqssd
end
