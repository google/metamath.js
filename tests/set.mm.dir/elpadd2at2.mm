include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "csn.mm"
include "co.mm"
include "wbr.mm"
include "wb.mm"
include "elpadd2at.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem elpadd2at2
  let cA: class A
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vs: setvar s
  let vq: setvar q
  let vr: setvar r
  let cX: class X
  let cY: class Y
  assume paddfval.l: |- .<_ = ( le ` K )
  assume paddfval.j: |- .\/ = ( join ` K )
  assume paddfval.a: |- A = ( Atoms ` K )
  assume paddfval.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. Lat /\ ( Q e. A /\ R e. A /\ S e. A ) ) -> ( S e. ( { Q } .+ { R } ) <-> S .<_ ( Q .\/ R ) ) )

  proof
    cK
    clat
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    w3a
    wa
    #
    cS
    cQ
    csn
    cR
    csn
    c.pl
    co
    wcel
    #
    @3
    cS
    cQ
    cR
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    @6
    @0
    @1
    @2
    @5
    @7
    wb
    @3
    cA
    c.pl
    cQ
    cR
    cS
    c.or
    cK
    c.le
    paddfval.l
    paddfval.j
    paddfval.a
    paddfval.p
    elpadd2at
    3adant3r3
    @4
    @3
    @6
    @0
    @1
    @2
    @3
    simpr3
    biantrurd
    bitr4d
end
