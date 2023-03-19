include "chmeo.mm"
include "co.mm"
include "wcel.mm"
include "cuni.mm"
include "ctop.mm"
include "ctopon.mm"
include "cfv.mm"
include "ccn.mm"
include "hmeocn.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "wf1o.mm"
include "wfo.mm"
include "crn.mm"
include "wceq.mm"
include "hmeof1o.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "cv.mm"
include "hmeoima.mm"
include "qtopomap.mm"

theorem hmeoqtop
  let cF: class F
  let cJ: class J
  let cK: class K
  let vx: setvar x


  assert |- ( F e. ( J Homeo K ) -> K = ( J qTop F ) )

  proof
    cF
    cJ
    cK
    chmeo
    co
    wcel
    #
    vx
    cF
    cJ
    cK
    cK
    cuni
    #
    @0
    cK
    ctop
    wcel
    #
    cK
    @1
    ctopon
    cfv
    wcel
    @0
    cF
    cJ
    cK
    ccn
    co
    wcel
    @2
    cF
    cJ
    cK
    hmeocn
    #
    cF
    cJ
    cK
    cntop2
    syl
    cK
    @1
    @1
    eqid
    #
    toptopon
    sylib
    @3
    @0
    cJ
    cuni
    #
    @1
    cF
    wf1o
    @5
    @1
    cF
    wfo
    cF
    crn
    @1
    wceq
    cF
    cJ
    cK
    @5
    @1
    @5
    eqid
    @4
    hmeof1o
    @5
    @1
    cF
    f1ofo
    @5
    @1
    cF
    forn
    3syl
    vx
    cv
    cF
    cJ
    cK
    hmeoima
    qtopomap
end
