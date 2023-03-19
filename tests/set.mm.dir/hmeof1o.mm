include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "chmeo.mm"
include "co.mm"
include "wf1o.mm"
include "ccn.mm"
include "hmeocn.mm"
include "ctop.mm"
include "cntop1.mm"
include "toptopon.mm"
include "sylib.mm"
include "cntop2.mm"
include "jca.mm"
include "syl.mm"
include "hmeof1o2.mm"
include "3expia.mm"
include "mpcom.mm"

theorem hmeof1o
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  assume hmeof1o.1: |- X = U. J
  assume hmeof1o.2: |- Y = U. K


  assert |- ( F e. ( J Homeo K ) -> F : X -1-1-onto-> Y )

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
    wa
    #
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    cX
    cY
    cF
    wf1o
    #
    @3
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @2
    cF
    cJ
    cK
    hmeocn
    @5
    @0
    @1
    @5
    cJ
    ctop
    wcel
    @0
    cF
    cJ
    cK
    cntop1
    cJ
    cX
    hmeof1o.1
    toptopon
    sylib
    @5
    cK
    ctop
    wcel
    @1
    cF
    cJ
    cK
    cntop2
    cK
    cY
    hmeof1o.2
    toptopon
    sylib
    jca
    syl
    @0
    @1
    @3
    @4
    cF
    cJ
    cK
    cX
    cY
    hmeof1o2
    3expia
    mpcom
end
