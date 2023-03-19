include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "chmeo.mm"
include "co.mm"
include "w3a.mm"
include "wfn.mm"
include "ccnv.mm"
include "wf1o.mm"
include "wf.mm"
include "ccn.mm"
include "hmeocn.mm"
include "cnf2.mm"
include "syl3an3.mm"
include "ffn.mm"
include "syl.mm"
include "hmeocnvcn.mm"
include "3com12.mm"
include "dff1o4.mm"
include "sylanbrc.mm"

theorem hmeof1o2
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y


  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ F e. ( J Homeo K ) ) -> F : X -1-1-onto-> Y )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    w3a
    #
    cF
    cX
    wfn
    #
    cF
    ccnv
    #
    cY
    wfn
    #
    cX
    cY
    cF
    wf1o
    @3
    cX
    cY
    cF
    wf
    #
    @4
    @2
    @0
    @1
    cF
    cJ
    cK
    ccn
    co
    wcel
    @7
    cF
    cJ
    cK
    hmeocn
    cF
    cJ
    cK
    cX
    cY
    cnf2
    syl3an3
    cX
    cY
    cF
    ffn
    syl
    @3
    cY
    cX
    @5
    wf
    #
    @6
    @2
    @0
    @1
    @5
    cK
    cJ
    ccn
    co
    wcel
    #
    @8
    cF
    cJ
    cK
    hmeocnvcn
    @1
    @0
    @9
    @8
    @5
    cK
    cJ
    cY
    cX
    cnf2
    3com12
    syl3an3
    cY
    cX
    @5
    ffn
    syl
    cX
    cY
    cF
    dff1o4
    sylanbrc
end
