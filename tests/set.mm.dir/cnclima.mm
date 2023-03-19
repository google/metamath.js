include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cuni.mm"
include "cdif.mm"
include "wf.mm"
include "wceq.mm"
include "eqid.mm"
include "cnf.mm"
include "adantr.mm"
include "wfun.mm"
include "ffun.mm"
include "funcnvcnv.mm"
include "imadif.mm"
include "3syl.mm"
include "fimacnv.mm"
include "difeq1d.mm"
include "eqtr2d.mm"
include "syl.mm"
include "cldopn.mm"
include "cnima.mm"
include "sylan2.mm"
include "eqeltrd.mm"
include "ctop.mm"
include "wss.mm"
include "wb.mm"
include "cntop1.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "iscld2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem cnclima
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K


  assert |- ( ( F e. ( J Cn K ) /\ A e. ( Clsd ` K ) ) -> ( `' F " A ) e. ( Clsd ` J ) )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cA
    cK
    ccld
    cfv
    wcel
    #
    wa
    #
    cF
    ccnv
    #
    cA
    cima
    #
    cJ
    ccld
    cfv
    wcel
    #
    cJ
    cuni
    #
    @4
    cdif
    #
    cJ
    wcel
    #
    @2
    @7
    @3
    cK
    cuni
    #
    cA
    cdif
    #
    cima
    #
    cJ
    @2
    @6
    @9
    cF
    wf
    #
    @7
    @11
    wceq
    @0
    @12
    @1
    cF
    cJ
    cK
    @6
    @9
    @6
    eqid
    #
    @9
    eqid
    #
    cnf
    adantr
    #
    @12
    @11
    @3
    @9
    cima
    #
    @4
    cdif
    #
    @7
    @12
    cF
    wfun
    @3
    ccnv
    wfun
    @11
    @17
    wceq
    @6
    @9
    cF
    ffun
    cF
    funcnvcnv
    @9
    cA
    @3
    imadif
    3syl
    @12
    @16
    @6
    @4
    @6
    @9
    cF
    fimacnv
    difeq1d
    eqtr2d
    syl
    @1
    @0
    @10
    cK
    wcel
    @11
    cJ
    wcel
    cA
    cK
    @9
    @14
    cldopn
    @10
    cF
    cJ
    cK
    cnima
    sylan2
    eqeltrd
    @2
    cJ
    ctop
    wcel
    #
    @4
    @6
    wss
    @5
    @8
    wb
    @0
    @18
    @1
    cF
    cJ
    cK
    cntop1
    adantr
    @2
    cF
    cdm
    #
    @4
    @6
    cF
    cA
    cnvimass
    @2
    @12
    @19
    @6
    wceq
    @15
    @6
    @9
    cF
    fdm
    syl
    syl5sseq
    @4
    cJ
    @6
    @13
    iscld2
    syl2anc
    mpbird
end
