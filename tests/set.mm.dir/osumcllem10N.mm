include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wn.mm"
include "wne.mm"
include "csn.mm"
include "simp11.mm"
include "simp2.mm"
include "snssd.mm"
include "simp12.mm"
include "sspadd2.mm"
include "syl3anc.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "sspadd1.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "ssneldd.mm"
include "nelne1.mm"
include "syl2anc.mm"

theorem osumcllem10N
  let cA: class A
  let cC: class C
  let c.pl: class .+
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume osumcllem.l: |- .<_ = ( le ` K )
  assume osumcllem.j: |- .\/ = ( join ` K )
  assume osumcllem.a: |- A = ( Atoms ` K )
  assume osumcllem.p: |- .+ = ( +P ` K )
  assume osumcllem.o: |- ._|_ = ( _|_P ` K )
  assume osumcllem.c: |- C = ( PSubCl ` K )
  assume osumcllem.m: |- M = ( X .+ { p } )
  assume osumcllem.u: |- U = ( ._|_ ` ( ._|_ ` ( X .+ Y ) ) )


  assert |- ( ( ( K e. HL /\ X C_ A /\ Y C_ A ) /\ p e. A /\ -. p e. ( X .+ Y ) ) -> M =/= X )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    w3a
    #
    vp
    cv
    #
    cA
    wcel
    #
    @4
    cX
    cY
    c.pl
    co
    #
    wcel
    wn
    #
    w3a
    #
    @4
    cM
    wcel
    @4
    cX
    wcel
    wn
    cM
    cX
    wne
    @8
    @4
    cX
    @4
    csn
    #
    c.pl
    co
    #
    cM
    @8
    @9
    @10
    wss
    #
    @4
    @10
    wcel
    @8
    @0
    @9
    cA
    wss
    @1
    @11
    @0
    @1
    @2
    @5
    @7
    simp11
    @8
    @4
    cA
    @3
    @5
    @7
    simp2
    snssd
    @0
    @1
    @2
    @5
    @7
    simp12
    cA
    chlt
    c.pl
    cK
    @9
    cX
    osumcllem.a
    osumcllem.p
    sspadd2
    syl3anc
    @4
    @10
    vp
    vex
    snss
    sylibr
    osumcllem.m
    syl6eleqr
    @8
    cX
    @6
    @4
    @3
    @5
    cX
    @6
    wss
    @7
    cA
    chlt
    c.pl
    cK
    cX
    cY
    osumcllem.a
    osumcllem.p
    sspadd1
    3ad2ant1
    @3
    @5
    @7
    simp3
    ssneldd
    @4
    cM
    cX
    nelne1
    syl2anc
end
