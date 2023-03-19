include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wral.mm"
include "eqid.mm"
include "hlsuprexch.mm"
include "simpld.mm"
include "imp.mm"

theorem hlsupr
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vr: setvar r
  assume hlsupr.l: |- .<_ = ( le ` K )
  assume hlsupr.j: |- .\/ = ( join ` K )
  assume hlsupr.a: |- A = ( Atoms ` K )

  disjoint A r
  disjoint K r
  disjoint P r
  disjoint Q r
  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ P =/= Q ) -> E. r e. A ( r =/= P /\ r =/= Q /\ r .<_ ( P .\/ Q ) ) )

  proof
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    w3a
    #
    cP
    cQ
    wne
    #
    vr
    cv
    #
    cP
    wne
    @2
    cQ
    wne
    @2
    cP
    cQ
    c.or
    co
    c.le
    wbr
    w3a
    vr
    cA
    wrex
    #
    @0
    @1
    @3
    wi
    cP
    @2
    c.le
    wbr
    wn
    cP
    @2
    cQ
    c.or
    co
    c.le
    wbr
    wa
    cQ
    @2
    cP
    c.or
    co
    c.le
    wbr
    wi
    vr
    cK
    cbs
    cfv
    #
    wral
    vr
    cA
    @4
    cP
    cQ
    c.or
    cK
    c.le
    @4
    eqid
    hlsupr.l
    hlsupr.j
    hlsupr.a
    hlsuprexch
    simpld
    imp
end
