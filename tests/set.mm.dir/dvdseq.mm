include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cn0.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "dvdsabseq.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "absidd.mm"
include "adantr.mm"
include "eqcomd.mm"
include "simpr.mm"
include "ad2antlr.mm"
include "3eqtrd.mm"
include "sylan2.mm"

theorem dvdseq
  let cM: class M
  let cN: class N


  assert |- ( ( ( M e. NN0 /\ N e. NN0 ) /\ ( M || N /\ N || M ) ) -> M = N )

  proof
    cM
    cN
    cdvds
    wbr
    cN
    cM
    cdvds
    wbr
    wa
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cM
    cabs
    cfv
    #
    cN
    cabs
    cfv
    #
    wceq
    #
    cM
    cN
    wceq
    cM
    cN
    dvdsabseq
    @2
    @5
    wa
    cM
    @3
    @4
    cN
    @2
    cM
    @3
    wceq
    @5
    @2
    @3
    cM
    @0
    @3
    cM
    wceq
    @1
    @0
    cM
    cM
    nn0re
    cM
    nn0ge0
    absidd
    adantr
    eqcomd
    adantr
    @2
    @5
    simpr
    @1
    @4
    cN
    wceq
    @0
    @5
    @1
    cN
    cN
    nn0re
    cN
    nn0ge0
    absidd
    ad2antlr
    3eqtrd
    sylan2
end
