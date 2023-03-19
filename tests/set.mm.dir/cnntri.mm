include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ctop.mm"
include "ccnv.mm"
include "cima.mm"
include "cuni.mm"
include "cnt.mm"
include "cfv.mm"
include "cntop1.mm"
include "adantr.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wceq.mm"
include "wf.mm"
include "eqid.mm"
include "cnf.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "cntop2.mm"
include "ntropn.mm"
include "sylan.mm"
include "cnima.mm"
include "syldan.mm"
include "ntrss2.mm"
include "imass2.mm"
include "ssntr.mm"
include "syl22anc.mm"

theorem cnntri
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let cY: class Y
  assume cncls2i.1: |- Y = U. K


  assert |- ( ( F e. ( J Cn K ) /\ S C_ Y ) -> ( `' F " ( ( int ` K ) ` S ) ) C_ ( ( int ` J ) ` ( `' F " S ) ) )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cS
    cY
    wss
    #
    wa
    #
    cJ
    ctop
    wcel
    #
    cF
    ccnv
    #
    cS
    cima
    #
    cJ
    cuni
    #
    wss
    @4
    cS
    cK
    cnt
    cfv
    cfv
    #
    cima
    #
    cJ
    wcel
    #
    @8
    @5
    wss
    #
    @8
    @5
    cJ
    cnt
    cfv
    cfv
    wss
    @0
    @3
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
    @5
    @6
    cF
    cS
    cnvimass
    @0
    @11
    @6
    wceq
    #
    @1
    @0
    @6
    cY
    cF
    wf
    @12
    cF
    cJ
    cK
    @6
    cY
    @6
    eqid
    #
    cncls2i.1
    cnf
    @6
    cY
    cF
    fdm
    syl
    adantr
    syl5sseq
    @0
    @1
    @7
    cK
    wcel
    #
    @9
    @0
    cK
    ctop
    wcel
    #
    @1
    @14
    cF
    cJ
    cK
    cntop2
    #
    cS
    cK
    cY
    cncls2i.1
    ntropn
    sylan
    @7
    cF
    cJ
    cK
    cnima
    syldan
    @2
    @7
    cS
    wss
    #
    @10
    @0
    @15
    @1
    @17
    @16
    cS
    cK
    cY
    cncls2i.1
    ntrss2
    sylan
    @7
    cS
    @4
    imass2
    syl
    @5
    cJ
    @8
    @6
    @13
    ssntr
    syl22anc
end
