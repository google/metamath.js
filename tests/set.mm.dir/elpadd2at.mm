include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "co.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "snssd.mm"
include "simp3.mm"
include "snnzg.mm"
include "3ad2ant2.mm"
include "elpaddat.mm"
include "syl31anc.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "rexsng.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem elpadd2at
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


  assert |- ( ( K e. Lat /\ Q e. A /\ R e. A ) -> ( S e. ( { Q } .+ { R } ) <-> ( S e. A /\ S .<_ ( Q .\/ R ) ) ) )

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
    w3a
    #
    cS
    cQ
    csn
    #
    cR
    csn
    c.pl
    co
    wcel
    #
    cS
    cA
    wcel
    #
    cS
    vr
    cv
    #
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    vr
    @4
    wrex
    #
    wa
    #
    @6
    cS
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    @3
    @0
    @4
    cA
    wss
    @2
    @4
    c0
    wne
    #
    @5
    @11
    wb
    @0
    @1
    @2
    simp1
    @3
    cQ
    cA
    @0
    @1
    @2
    simp2
    snssd
    @0
    @1
    @2
    simp3
    @1
    @0
    @14
    @2
    cQ
    cA
    snnzg
    3ad2ant2
    cA
    c.pl
    cR
    cS
    c.or
    cK
    c.le
    @4
    vr
    paddfval.l
    paddfval.j
    paddfval.a
    paddfval.p
    elpaddat
    syl31anc
    @3
    @10
    @13
    @6
    @1
    @0
    @10
    @13
    wb
    @2
    @9
    @13
    vr
    cQ
    cA
    @7
    cQ
    wceq
    @8
    @12
    cS
    c.le
    @7
    cQ
    cR
    c.or
    oveq1
    breq2d
    rexsng
    3ad2ant2
    anbi2d
    bitrd
end
