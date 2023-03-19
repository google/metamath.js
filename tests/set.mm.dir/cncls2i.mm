include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccnv.mm"
include "ccl.mm"
include "cfv.mm"
include "cima.mm"
include "ccld.mm"
include "ctop.mm"
include "cntop2.mm"
include "clscld.mm"
include "sylan.mm"
include "cnclima.mm"
include "syldan.mm"
include "sscls.mm"
include "imass2.mm"
include "syl.mm"
include "cuni.mm"
include "eqid.mm"
include "clsss2.mm"
include "syl2anc.mm"

theorem cncls2i
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let cY: class Y
  assume cncls2i.1: |- Y = U. K


  assert |- ( ( F e. ( J Cn K ) /\ S C_ Y ) -> ( ( cls ` J ) ` ( `' F " S ) ) C_ ( `' F " ( ( cls ` K ) ` S ) ) )

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
    cF
    ccnv
    #
    cS
    cK
    ccl
    cfv
    cfv
    #
    cima
    #
    cJ
    ccld
    cfv
    wcel
    #
    @3
    cS
    cima
    #
    @5
    wss
    #
    @7
    cJ
    ccl
    cfv
    cfv
    @5
    wss
    @0
    @1
    @4
    cK
    ccld
    cfv
    wcel
    #
    @6
    @0
    cK
    ctop
    wcel
    #
    @1
    @9
    cF
    cJ
    cK
    cntop2
    #
    cS
    cK
    cY
    cncls2i.1
    clscld
    sylan
    @4
    cF
    cJ
    cK
    cnclima
    syldan
    @2
    cS
    @4
    wss
    #
    @8
    @0
    @10
    @1
    @12
    @11
    cS
    cK
    cY
    cncls2i.1
    sscls
    sylan
    cS
    @4
    @3
    imass2
    syl
    @5
    @7
    cJ
    cJ
    cuni
    #
    @13
    eqid
    clsss2
    syl2anc
end
