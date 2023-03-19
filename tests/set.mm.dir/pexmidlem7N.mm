include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "co.mm"
include "wn.mm"
include "wa.mm"
include "csn.mm"
include "simpl1.mm"
include "simpl3.mm"
include "snssd.mm"
include "simpl2.mm"
include "sspadd2.mm"
include "syl3anc.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "polssatN.mm"
include "syl2anc.mm"
include "sspadd1.mm"
include "simpr3.mm"
include "ssneldd.mm"
include "nelne1.mm"

theorem pexmidlem7N
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume pexmidlem.l: |- .<_ = ( le ` K )
  assume pexmidlem.j: |- .\/ = ( join ` K )
  assume pexmidlem.a: |- A = ( Atoms ` K )
  assume pexmidlem.p: |- .+ = ( +P ` K )
  assume pexmidlem.o: |- ._|_ = ( _|_P ` K )
  assume pexmidlem.m: |- M = ( X .+ { p } )


  assert |- ( ( ( K e. HL /\ X C_ A /\ p e. A ) /\ ( ( ._|_ ` ( ._|_ ` X ) ) = X /\ X =/= (/) /\ -. p e. ( X .+ ( ._|_ ` X ) ) ) ) -> M =/= X )

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
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    cX
    wceq
    #
    cX
    c0
    wne
    #
    @2
    cX
    @5
    c.pl
    co
    #
    wcel
    wn
    #
    w3a
    #
    wa
    #
    @2
    cM
    wcel
    @2
    cX
    wcel
    wn
    cM
    cX
    wne
    @11
    @2
    cX
    @2
    csn
    #
    c.pl
    co
    #
    cM
    @11
    @12
    @13
    wss
    #
    @2
    @13
    wcel
    @11
    @0
    @12
    cA
    wss
    @1
    @14
    @0
    @1
    @3
    @10
    simpl1
    #
    @11
    @2
    cA
    @0
    @1
    @3
    @10
    simpl3
    snssd
    @0
    @1
    @3
    @10
    simpl2
    #
    cA
    chlt
    c.pl
    cK
    @12
    cX
    pexmidlem.a
    pexmidlem.p
    sspadd2
    syl3anc
    @2
    @13
    vp
    vex
    snss
    sylibr
    pexmidlem.m
    syl6eleqr
    @11
    cX
    @8
    @2
    @11
    @0
    @1
    @5
    cA
    wss
    #
    cX
    @8
    wss
    @15
    @16
    @11
    @0
    @1
    @17
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
    cA
    chlt
    c.pl
    cK
    cX
    @5
    pexmidlem.a
    pexmidlem.p
    sspadd1
    syl3anc
    @4
    @6
    @7
    @9
    simpr3
    ssneldd
    @2
    cM
    cX
    nelne1
    syl2anc
end
