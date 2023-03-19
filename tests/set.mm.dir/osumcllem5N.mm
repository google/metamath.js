include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "clat.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "simp12.mm"
include "simp13.mm"
include "simp31.mm"
include "simp32.mm"
include "simp2.mm"
include "simp33.mm"
include "elpaddri.mm"
include "syl322anc.mm"

theorem osumcllem5N
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
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assume osumcllem.l: |- .<_ = ( le ` K )
  assume osumcllem.j: |- .\/ = ( join ` K )
  assume osumcllem.a: |- A = ( Atoms ` K )
  assume osumcllem.p: |- .+ = ( +P ` K )
  assume osumcllem.o: |- ._|_ = ( _|_P ` K )
  assume osumcllem.c: |- C = ( PSubCl ` K )
  assume osumcllem.m: |- M = ( X .+ { p } )
  assume osumcllem.u: |- U = ( ._|_ ` ( ._|_ ` ( X .+ Y ) ) )


  assert |- ( ( ( K e. HL /\ X C_ A /\ Y C_ A ) /\ p e. A /\ ( r e. X /\ q e. Y /\ p .<_ ( r .\/ q ) ) ) -> p e. ( X .+ Y ) )

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
    vr
    cv
    #
    cX
    wcel
    #
    vq
    cv
    #
    cY
    wcel
    #
    @4
    @6
    @8
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cK
    clat
    wcel
    #
    @1
    @2
    @7
    @9
    @5
    @10
    @4
    cX
    cY
    c.pl
    co
    wcel
    @12
    @0
    @13
    @0
    @1
    @2
    @5
    @11
    simp11
    cK
    hllat
    syl
    @0
    @1
    @2
    @5
    @11
    simp12
    @0
    @1
    @2
    @5
    @11
    simp13
    @3
    @5
    @7
    @9
    @10
    simp31
    @3
    @5
    @7
    @9
    @10
    simp32
    @3
    @5
    @11
    simp2
    @3
    @5
    @7
    @9
    @10
    simp33
    cA
    c.pl
    @6
    @8
    @4
    c.or
    cK
    c.le
    cX
    cY
    osumcllem.l
    osumcllem.j
    osumcllem.a
    osumcllem.p
    elpaddri
    syl322anc
end
