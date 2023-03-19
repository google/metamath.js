include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "ccn.mm"
include "ccnv.mm"
include "hmeocn.mm"
include "cnco.mm"
include "syl2an.mm"
include "cnvco.mm"
include "hmeocnvcn.mm"
include "syl2anr.mm"
include "syl5eqel.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem hmeoco
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L


  assert |- ( ( F e. ( J Homeo K ) /\ G e. ( K Homeo L ) ) -> ( G o. F ) e. ( J Homeo L ) )

  proof
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    cG
    cK
    cL
    chmeo
    co
    wcel
    #
    wa
    #
    cG
    cF
    ccom
    #
    cJ
    cL
    ccn
    co
    wcel
    #
    @3
    ccnv
    #
    cL
    cJ
    ccn
    co
    #
    wcel
    @3
    cJ
    cL
    chmeo
    co
    wcel
    @0
    cF
    cJ
    cK
    ccn
    co
    wcel
    cG
    cK
    cL
    ccn
    co
    wcel
    @4
    @1
    cF
    cJ
    cK
    hmeocn
    cG
    cK
    cL
    hmeocn
    cF
    cG
    cJ
    cK
    cL
    cnco
    syl2an
    @2
    @5
    cF
    ccnv
    #
    cG
    ccnv
    #
    ccom
    #
    @6
    cG
    cF
    cnvco
    @1
    @8
    cL
    cK
    ccn
    co
    wcel
    @7
    cK
    cJ
    ccn
    co
    wcel
    @9
    @6
    wcel
    @0
    cG
    cK
    cL
    hmeocnvcn
    cF
    cJ
    cK
    hmeocnvcn
    @8
    @7
    cL
    cK
    cJ
    cnco
    syl2anr
    syl5eqel
    @3
    cJ
    cL
    ishmeo
    sylanbrc
end
