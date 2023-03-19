include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "cnt.mm"
include "cfv.mm"
include "ccnv.mm"
include "ccn.mm"
include "cuni.mm"
include "hmeocn.mm"
include "adantr.mm"
include "crn.mm"
include "imassrn.mm"
include "wf1o.mm"
include "wfo.mm"
include "wceq.mm"
include "eqid.mm"
include "hmeof1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "syl5sseq.mm"
include "cnntri.mm"
include "syl2anc.mm"
include "wf1.mm"
include "f1of1.mm"
include "syl.mm"
include "f1imacnv.mm"
include "sylancom.mm"
include "fveq2d.mm"
include "sseqtrd.mm"
include "wfun.mm"
include "wi.mm"
include "f1ofun.mm"
include "ctop.mm"
include "cntop2.mm"
include "ntrss3.mm"
include "sseqtr4d.mm"
include "funimass1.mm"
include "mpd.mm"
include "hmeocnvcn.mm"
include "sylan.mm"
include "imacnvcnv.mm"
include "fveq2i.mm"
include "3sstr3g.mm"
include "eqssd.mm"

theorem hmeontr
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  assume hmeoopn.1: |- X = U. J


  assert |- ( ( F e. ( J Homeo K ) /\ A C_ X ) -> ( ( int ` K ) ` ( F " A ) ) = ( F " ( ( int ` J ) ` A ) ) )

  proof
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cF
    cA
    cima
    #
    cK
    cnt
    cfv
    #
    cfv
    #
    cF
    cA
    cJ
    cnt
    cfv
    #
    cfv
    #
    cima
    #
    @2
    cF
    ccnv
    #
    @5
    cima
    #
    @7
    wss
    #
    @5
    @8
    wss
    #
    @2
    @10
    @9
    @3
    cima
    #
    @6
    cfv
    #
    @7
    @2
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @3
    cK
    cuni
    #
    wss
    #
    @10
    @14
    wss
    @0
    @15
    @1
    cF
    cJ
    cK
    hmeocn
    adantr
    #
    @2
    cF
    crn
    #
    @3
    @16
    cF
    cA
    imassrn
    @2
    cX
    @16
    cF
    wf1o
    #
    cX
    @16
    cF
    wfo
    @19
    @16
    wceq
    @0
    @20
    @1
    cF
    cJ
    cK
    cX
    @16
    hmeoopn.1
    @16
    eqid
    #
    hmeof1o
    adantr
    #
    cX
    @16
    cF
    f1ofo
    cX
    @16
    cF
    forn
    3syl
    #
    syl5sseq
    #
    @3
    cF
    cJ
    cK
    @16
    @21
    cnntri
    syl2anc
    @2
    @13
    cA
    @6
    @0
    @1
    cX
    @16
    cF
    wf1
    #
    @13
    cA
    wceq
    @2
    @20
    @25
    @22
    cX
    @16
    cF
    f1of1
    syl
    cX
    @16
    cA
    cF
    f1imacnv
    sylancom
    fveq2d
    sseqtrd
    @2
    cF
    wfun
    #
    @5
    @19
    wss
    @11
    @12
    wi
    @2
    @20
    @26
    @22
    cX
    @16
    cF
    f1ofun
    syl
    @2
    @5
    @16
    @19
    @2
    cK
    ctop
    wcel
    #
    @17
    @5
    @16
    wss
    @2
    @15
    @27
    @18
    cF
    cJ
    cK
    cntop2
    syl
    @24
    @3
    cK
    @16
    @21
    ntrss3
    syl2anc
    @23
    sseqtr4d
    @5
    @7
    cF
    funimass1
    syl2anc
    mpd
    @2
    @9
    ccnv
    #
    @7
    cima
    #
    @28
    cA
    cima
    #
    @4
    cfv
    #
    @8
    @5
    @0
    @9
    cK
    cJ
    ccn
    co
    wcel
    @1
    @29
    @31
    wss
    cF
    cJ
    cK
    hmeocnvcn
    cA
    @9
    cK
    cJ
    cX
    hmeoopn.1
    cnntri
    sylan
    cF
    @7
    imacnvcnv
    @30
    @3
    @4
    cF
    cA
    imacnvcnv
    fveq2i
    3sstr3g
    eqssd
end
