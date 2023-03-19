include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "cint.mm"
include "c1o.mm"
include "cdom.mm"
include "wbr.mm"
include "c0.mm"
include "breq1.mm"
include "wne.mm"
include "wa.mm"
include "cen.mm"
include "cv.mm"
include "wex.mm"
include "csn.mm"
include "wceq.mm"
include "wss.mm"
include "uffixsn.mm"
include "intss1.mm"
include "syl.mm"
include "simpr.mm"
include "snssd.mm"
include "eqssd.mm"
include "ex.mm"
include "eximdv.mm"
include "n0.mm"
include "en1.mm"
include "3imtr4g.mm"
include "imp.mm"
include "endom.mm"
include "con0.mm"
include "1on.mm"
include "0domg.mm"
include "mp1i.mm"
include "pm2.61ne.mm"

theorem ufildom1
  let cF: class F
  let cX: class X
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( F e. ( UFil ` X ) -> |^| F ~<_ 1o )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    cF
    cint
    #
    c1o
    cdom
    wbr
    #
    c0
    c1o
    cdom
    wbr
    #
    @1
    c0
    @1
    c0
    c1o
    cdom
    breq1
    @0
    @1
    c0
    wne
    #
    wa
    @1
    c1o
    cen
    wbr
    #
    @2
    @0
    @4
    @5
    @0
    vx
    cv
    #
    @1
    wcel
    #
    vx
    wex
    @1
    @6
    csn
    #
    wceq
    #
    vx
    wex
    @4
    @5
    @0
    @7
    @9
    vx
    @0
    @7
    @9
    @0
    @7
    wa
    #
    @1
    @8
    @10
    @8
    cF
    wcel
    @1
    @8
    wss
    @6
    cF
    cX
    uffixsn
    @8
    cF
    intss1
    syl
    @10
    @6
    @1
    @0
    @7
    simpr
    snssd
    eqssd
    ex
    eximdv
    vx
    @1
    n0
    vx
    @1
    en1
    3imtr4g
    imp
    @1
    c1o
    endom
    syl
    c1o
    con0
    wcel
    @3
    @0
    1on
    c1o
    con0
    0domg
    mp1i
    pm2.61ne
end
