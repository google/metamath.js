include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "ccn.mm"
include "hmeocnvcn.mm"
include "wrel.mm"
include "wceq.mm"
include "cuni.mm"
include "wf.mm"
include "hmeocn.mm"
include "eqid.mm"
include "cnf.mm"
include "frel.mm"
include "3syl.mm"
include "dfrel2.mm"
include "sylib.mm"
include "eqeltrd.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem hmeocnv
  let cF: class F
  let cJ: class J
  let cK: class K


  assert |- ( F e. ( J Homeo K ) -> `' F e. ( K Homeo J ) )

  proof
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    cF
    ccnv
    #
    cK
    cJ
    ccn
    co
    wcel
    @1
    ccnv
    #
    cJ
    cK
    ccn
    co
    #
    wcel
    @1
    cK
    cJ
    chmeo
    co
    wcel
    cF
    cJ
    cK
    hmeocnvcn
    @0
    @2
    cF
    @3
    @0
    cF
    wrel
    #
    @2
    cF
    wceq
    @0
    cF
    @3
    wcel
    cJ
    cuni
    #
    cK
    cuni
    #
    cF
    wf
    @4
    cF
    cJ
    cK
    hmeocn
    #
    cF
    cJ
    cK
    @5
    @6
    @5
    eqid
    @6
    eqid
    cnf
    @5
    @6
    cF
    frel
    3syl
    cF
    dfrel2
    sylib
    @7
    eqeltrd
    @1
    cK
    cJ
    ishmeo
    sylanbrc
end
