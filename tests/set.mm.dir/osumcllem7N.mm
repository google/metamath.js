include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cin.mm"
include "co.mm"
include "wbr.mm"
include "wrex.mm"
include "clat.mm"
include "csn.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "simp12.mm"
include "simp23.mm"
include "simp22.mm"
include "inss2.mm"
include "sseli.mm"
include "3ad2ant3.mm"
include "syl6eleq.mm"
include "elpaddatiN.mm"
include "syl32anc.mm"
include "simp121.mm"
include "simp123.mm"
include "simp2.mm"
include "inss1.mm"
include "simp13.mm"
include "sseldi.mm"
include "simp3.mm"
include "osumcllem6N.mm"
include "syl123anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem osumcllem7N
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
  let vq: setvar q
  let vp: setvar p
  let vr: setvar r
  assume osumcllem.l: |- .<_ = ( le ` K )
  assume osumcllem.j: |- .\/ = ( join ` K )
  assume osumcllem.a: |- A = ( Atoms ` K )
  assume osumcllem.p: |- .+ = ( +P ` K )
  assume osumcllem.o: |- ._|_ = ( _|_P ` K )
  assume osumcllem.c: |- C = ( PSubCl ` K )
  assume osumcllem.m: |- M = ( X .+ { p } )
  assume osumcllem.u: |- U = ( ._|_ ` ( ._|_ ` ( X .+ Y ) ) )

  disjoint A q
  disjoint K q
  disjoint M q
  disjoint ._|_ q
  disjoint .+ q
  disjoint X q
  disjoint Y q
  disjoint p q
  disjoint q r
  disjoint A r
  disjoint .\/ r
  disjoint K r
  disjoint .<_ r
  disjoint M r
  disjoint ._|_ r
  disjoint .+ r
  disjoint X r
  disjoint Y r
  disjoint p r
  assert |- ( ( ( K e. HL /\ X C_ A /\ Y C_ A ) /\ ( X C_ ( ._|_ ` Y ) /\ X =/= (/) /\ p e. A ) /\ q e. ( Y i^i M ) ) -> p e. ( X .+ Y ) )

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
    cX
    c0
    wne
    #
    vp
    cv
    #
    cA
    wcel
    #
    w3a
    #
    vq
    cv
    #
    cY
    cM
    cin
    #
    wcel
    #
    w3a
    #
    @9
    vr
    cv
    #
    @6
    c.or
    co
    c.le
    wbr
    #
    vr
    cX
    wrex
    #
    @6
    cX
    cY
    c.pl
    co
    wcel
    #
    @12
    cK
    clat
    wcel
    #
    @1
    @7
    @5
    @9
    cX
    @6
    csn
    c.pl
    co
    #
    wcel
    @15
    @12
    @0
    @17
    @0
    @1
    @2
    @8
    @11
    simp11
    cK
    hllat
    syl
    @0
    @1
    @2
    @8
    @11
    simp12
    @3
    @4
    @5
    @7
    @11
    simp23
    @3
    @4
    @5
    @7
    @11
    simp22
    @12
    @9
    cM
    @18
    @11
    @3
    @9
    cM
    wcel
    @8
    @10
    cM
    @9
    cY
    cM
    inss2
    sseli
    3ad2ant3
    osumcllem.m
    syl6eleq
    cA
    c.pl
    @6
    @9
    c.or
    cK
    c.le
    cX
    vr
    osumcllem.l
    osumcllem.j
    osumcllem.a
    osumcllem.p
    elpaddatiN
    syl32anc
    @12
    @14
    @16
    vr
    cX
    @12
    @13
    cX
    wcel
    #
    @14
    w3a
    #
    @3
    @4
    @7
    @19
    @9
    cY
    wcel
    @14
    @16
    @3
    @8
    @11
    @19
    @14
    simp11
    @4
    @5
    @7
    @3
    @11
    @19
    @14
    simp121
    @4
    @5
    @7
    @3
    @11
    @19
    @14
    simp123
    @12
    @19
    @14
    simp2
    @20
    @10
    cY
    @9
    cY
    cM
    inss1
    @3
    @8
    @11
    @19
    @14
    simp13
    sseldi
    @12
    @19
    @14
    simp3
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
    osumcllem6N
    syl123anc
    rexlimdv3a
    mpd
end
