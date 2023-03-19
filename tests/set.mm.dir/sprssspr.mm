include "cvv.mm"
include "wcel.mm"
include "cspr.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "wss.mm"
include "wrex.mm"
include "sprval.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "r2ex.mm"
include "simpr.mm"
include "2eximi.mm"
include "sylbi.mm"
include "ax-gen.mm"
include "a1i.mm"
include "ss2ab.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "0ss.mm"
include "pm2.61i.mm"

theorem sprssspr
  let cV: class V
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let cW: class W
  let vk: setvar k
  let vx: setvar x

  disjoint V a
  disjoint V b
  disjoint V p
  disjoint a b
  disjoint a p
  disjoint b p
  disjoint W a
  disjoint W b
  disjoint W p
  disjoint k x
  assert |- ( Pairs ` V ) C_ { p | E. a E. b p = { a , b } }

  proof
    cV
    cvv
    wcel
    #
    cV
    cspr
    cfv
    #
    vp
    cv
    va
    cv
    #
    vb
    cv
    #
    cpr
    wceq
    #
    vb
    wex
    va
    wex
    #
    vp
    cab
    #
    wss
    @0
    @1
    @4
    vb
    cV
    wrex
    va
    cV
    wrex
    #
    vp
    cab
    #
    @6
    cV
    cvv
    vp
    va
    vb
    sprval
    @0
    @7
    @5
    wi
    #
    vp
    wal
    #
    @8
    @6
    wss
    @10
    @0
    @9
    vp
    @7
    @2
    cV
    wcel
    @3
    cV
    wcel
    wa
    #
    @4
    wa
    #
    vb
    wex
    va
    wex
    @5
    @4
    va
    vb
    cV
    cV
    r2ex
    @12
    @4
    va
    vb
    @11
    @4
    simpr
    2eximi
    sylbi
    ax-gen
    a1i
    @7
    @5
    vp
    ss2ab
    sylibr
    eqsstrd
    @0
    wn
    #
    @1
    c0
    @6
    cV
    cspr
    fvprc
    c0
    @6
    wss
    @13
    @6
    0ss
    a1i
    eqsstrd
    pm2.61i
end
