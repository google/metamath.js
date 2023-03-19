include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2r.mm"
include "simp31.mm"
include "simp32.mm"
include "wne.mm"
include "sseldd.mm"
include "3jca.mm"
include "simp2l.mm"
include "osumcllem4N.mm"
include "syl32anc.mm"
include "simp33.mm"
include "hlatexch1.mm"
include "sylc.mm"
include "osumcllem5N.mm"
include "syl313anc.mm"

theorem osumcllem6N
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


  assert |- ( ( ( K e. HL /\ X C_ A /\ Y C_ A ) /\ ( X C_ ( ._|_ ` Y ) /\ p e. A ) /\ ( r e. X /\ q e. Y /\ q .<_ ( r .\/ p ) ) ) -> p e. ( X .+ Y ) )

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
    cX
    cY
    c.pe
    cfv
    wss
    #
    vp
    cv
    #
    cA
    wcel
    #
    wa
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
    @10
    @8
    @5
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    @0
    @1
    @2
    @6
    @9
    @11
    @5
    @8
    @10
    c.or
    co
    c.le
    wbr
    #
    @5
    cX
    cY
    c.pl
    co
    wcel
    @0
    @1
    @2
    @7
    @13
    simp11
    #
    @0
    @1
    @2
    @7
    @13
    simp12
    #
    @0
    @1
    @2
    @7
    @13
    simp13
    #
    @3
    @4
    @6
    @13
    simp2r
    #
    @3
    @7
    @9
    @11
    @12
    simp31
    #
    @3
    @7
    @9
    @11
    @12
    simp32
    #
    @14
    @0
    @10
    cA
    wcel
    #
    @6
    @8
    cA
    wcel
    #
    w3a
    #
    @10
    @8
    wne
    #
    w3a
    @12
    @15
    @14
    @0
    @24
    @25
    @16
    @14
    @22
    @6
    @23
    @14
    cY
    cA
    @10
    @18
    @21
    sseldd
    @19
    @14
    cX
    cA
    @8
    @17
    @20
    sseldd
    3jca
    @14
    @0
    @2
    @4
    @9
    @11
    @25
    @16
    @18
    @3
    @4
    @6
    @13
    simp2l
    @20
    @21
    cA
    cC
    c.pl
    cU
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    cY
    vr
    vq
    vp
    osumcllem.l
    osumcllem.j
    osumcllem.a
    osumcllem.p
    osumcllem.o
    osumcllem.c
    osumcllem.m
    osumcllem.u
    osumcllem4N
    syl32anc
    3jca
    @3
    @7
    @9
    @11
    @12
    simp33
    cA
    @10
    @5
    @8
    c.or
    cK
    c.le
    osumcllem.l
    osumcllem.j
    osumcllem.a
    hlatexch1
    sylc
    cA
    cC
    c.pl
    cU
    c.or
    cK
    c.le
    cM
    c.pe
    cX
    cY
    vr
    vq
    vp
    osumcllem.l
    osumcllem.j
    osumcllem.a
    osumcllem.p
    osumcllem.o
    osumcllem.c
    osumcllem.m
    osumcllem.u
    osumcllem5N
    syl313anc
end
