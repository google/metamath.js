include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "wne.mm"
include "wi.mm"
include "simpl1.mm"
include "simpl2.mm"
include "polssatN.mm"
include "syl2anc.mm"
include "simprr.mm"
include "sseldd.mm"
include "simpl3.mm"
include "simprl.mm"
include "pexmidlem1N.mm"
include "3adantl3.mm"
include "hlatexch1.mm"
include "syl131anc.mm"
include "3impia.mm"
include "pexmidlem2N.mm"
include "syl13anc.mm"

theorem pexmidlem3N
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assume pexmidlem.l: |- .<_ = ( le ` K )
  assume pexmidlem.j: |- .\/ = ( join ` K )
  assume pexmidlem.a: |- A = ( Atoms ` K )
  assume pexmidlem.p: |- .+ = ( +P ` K )
  assume pexmidlem.o: |- ._|_ = ( _|_P ` K )
  assume pexmidlem.m: |- M = ( X .+ { p } )


  assert |- ( ( ( K e. HL /\ X C_ A /\ p e. A ) /\ ( r e. X /\ q e. ( ._|_ ` X ) ) /\ q .<_ ( r .\/ p ) ) -> p e. ( X .+ ( ._|_ ` X ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    vp
    cv
    #
    cA
    wcel
    #
    w3a
    #
    vr
    cv
    #
    cX
    wcel
    #
    vq
    cv
    #
    cX
    c.pe
    cfv
    #
    wcel
    #
    wa
    #
    @7
    @5
    @2
    c.or
    co
    c.le
    wbr
    #
    w3a
    @4
    @6
    @9
    @2
    @5
    @7
    c.or
    co
    c.le
    wbr
    #
    @2
    cX
    @8
    c.pl
    co
    wcel
    @4
    @10
    @11
    simp1
    @4
    @6
    @9
    @11
    simp2l
    @4
    @6
    @9
    @11
    simp2r
    @4
    @10
    @11
    @12
    @4
    @10
    wa
    #
    @0
    @7
    cA
    wcel
    @3
    @5
    cA
    wcel
    @7
    @5
    wne
    #
    @11
    @12
    wi
    @0
    @1
    @3
    @10
    simpl1
    #
    @13
    @8
    cA
    @7
    @13
    @0
    @1
    @8
    cA
    wss
    @15
    @0
    @1
    @3
    @10
    simpl2
    #
    cA
    cK
    c.pe
    cX
    pexmidlem.a
    pexmidlem.o
    polssatN
    syl2anc
    @4
    @6
    @9
    simprr
    sseldd
    @0
    @1
    @3
    @10
    simpl3
    @13
    cX
    cA
    @5
    @16
    @4
    @6
    @9
    simprl
    sseldd
    @0
    @1
    @10
    @14
    @3
    cA
    c.pl
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    vr
    vq
    vp
    pexmidlem.l
    pexmidlem.j
    pexmidlem.a
    pexmidlem.p
    pexmidlem.o
    pexmidlem.m
    pexmidlem1N
    3adantl3
    cA
    @7
    @2
    @5
    c.or
    cK
    c.le
    pexmidlem.l
    pexmidlem.j
    pexmidlem.a
    hlatexch1
    syl131anc
    3impia
    cA
    c.pl
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    vr
    vq
    vp
    pexmidlem.l
    pexmidlem.j
    pexmidlem.a
    pexmidlem.p
    pexmidlem.o
    pexmidlem.m
    pexmidlem2N
    syl13anc
end
