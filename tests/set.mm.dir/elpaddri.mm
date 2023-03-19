include "clat.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "simp3l.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3r.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "ne0i.mm"
include "anim12i.mm"
include "anim2i.mm"
include "3adant3.mm"
include "elpaddn0.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem elpaddri
  let cA: class A
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vs: setvar s
  let vq: setvar q
  let vr: setvar r
  assume paddfval.l: |- .<_ = ( le ` K )
  assume paddfval.j: |- .\/ = ( join ` K )
  assume paddfval.a: |- A = ( Atoms ` K )
  assume paddfval.p: |- .+ = ( +P ` K )


  assert |- ( ( ( K e. Lat /\ X C_ A /\ Y C_ A ) /\ ( Q e. X /\ R e. Y ) /\ ( S e. A /\ S .<_ ( Q .\/ R ) ) ) -> S e. ( X .+ Y ) )

  proof
    cK
    clat
    wcel
    cX
    cA
    wss
    cY
    cA
    wss
    w3a
    #
    cQ
    cX
    wcel
    #
    cR
    cY
    wcel
    #
    wa
    #
    cS
    cA
    wcel
    #
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
    #
    w3a
    #
    cS
    cX
    cY
    c.pl
    co
    wcel
    #
    @4
    cS
    vq
    cv
    #
    vr
    cv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    vr
    cY
    wrex
    vq
    cX
    wrex
    #
    @0
    @3
    @4
    @6
    simp3l
    @8
    @1
    @2
    @6
    @14
    @0
    @1
    @2
    @7
    simp2l
    @0
    @1
    @2
    @7
    simp2r
    @0
    @3
    @4
    @6
    simp3r
    @13
    @6
    cS
    cQ
    @11
    c.or
    co
    #
    c.le
    wbr
    vq
    vr
    cQ
    cR
    cX
    cY
    @10
    cQ
    wceq
    @12
    @15
    cS
    c.le
    @10
    cQ
    @11
    c.or
    oveq1
    breq2d
    @11
    cR
    wceq
    @15
    @5
    cS
    c.le
    @11
    cR
    cQ
    c.or
    oveq2
    breq2d
    rspc2ev
    syl3anc
    @8
    @0
    cX
    c0
    wne
    #
    cY
    c0
    wne
    #
    wa
    #
    wa
    #
    @9
    @4
    @14
    wa
    wb
    @0
    @3
    @19
    @7
    @3
    @18
    @0
    @1
    @16
    @2
    @17
    cX
    cQ
    ne0i
    cY
    cR
    ne0i
    anim12i
    anim2i
    3adant3
    cA
    c.pl
    cS
    c.or
    cK
    c.le
    cX
    cY
    vr
    vq
    paddfval.l
    paddfval.j
    paddfval.a
    paddfval.p
    elpaddn0
    syl
    mpbir2and
end
