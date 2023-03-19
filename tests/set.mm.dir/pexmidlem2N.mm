include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "clat.mm"
include "simpl1.mm"
include "hllat.mm"
include "syl.mm"
include "simpl2.mm"
include "polssatN.mm"
include "syl2anc.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpl3.mm"
include "simpr3.mm"
include "elpaddri.mm"
include "syl322anc.mm"

theorem pexmidlem2N
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


  assert |- ( ( ( K e. HL /\ X C_ A /\ p e. A ) /\ ( r e. X /\ q e. ( ._|_ ` X ) /\ p .<_ ( r .\/ q ) ) ) -> p e. ( X .+ ( ._|_ ` X ) ) )

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
    @2
    @5
    @7
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    cK
    clat
    wcel
    #
    @1
    @8
    cA
    wss
    #
    @6
    @9
    @3
    @10
    @2
    cX
    @8
    c.pl
    co
    wcel
    @12
    @0
    @13
    @0
    @1
    @3
    @11
    simpl1
    #
    cK
    hllat
    syl
    @0
    @1
    @3
    @11
    simpl2
    #
    @12
    @0
    @1
    @14
    @15
    @16
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
    @10
    simpr1
    @4
    @6
    @9
    @10
    simpr2
    @0
    @1
    @3
    @11
    simpl3
    @4
    @6
    @9
    @10
    simpr3
    cA
    c.pl
    @5
    @7
    @2
    c.or
    cK
    c.le
    cX
    @8
    pexmidlem.l
    pexmidlem.j
    pexmidlem.a
    pexmidlem.p
    elpaddri
    syl322anc
end
