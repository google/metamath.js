include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "wrex.mm"
include "simpr2r.mm"
include "clat.mm"
include "wb.mm"
include "simpl1.mm"
include "hllat.mm"
include "syl.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl3.mm"
include "elpaddn0.mm"
include "syl31anc.mm"
include "mpbid.mm"
include "wi.mm"
include "simp11.mm"
include "simp12.mm"
include "simp21.mm"
include "simp31.mm"
include "jca.mm"
include "simp22l.mm"
include "simp32l.mm"
include "simp32r.mm"
include "3jca.mm"
include "simp23.mm"
include "simp33.mm"
include "paddasslem14.mm"
include "syl32anc.mm"
include "3expia.mm"
include "3expd.mm"
include "imp.mm"
include "rexlimdvv.mm"
include "expimpd.mm"
include "mpd.mm"

theorem paddasslem15
  let vx: setvar x
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vr: setvar r
  let vp: setvar p
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )
  assume paddasslem.p: |- .+ = ( +P ` K )


  assert |- ( ( ( K e. HL /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) /\ ( Y =/= (/) /\ Z =/= (/) ) ) /\ ( p e. A /\ ( x e. X /\ r e. ( Y .+ Z ) ) /\ p .<_ ( x .\/ r ) ) ) -> p e. ( ( X .+ Y ) .+ Z ) )

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
    cZ
    cA
    wss
    #
    w3a
    #
    cY
    c0
    wne
    cZ
    c0
    wne
    wa
    #
    w3a
    #
    vp
    cv
    #
    cA
    wcel
    #
    vx
    cv
    #
    cX
    wcel
    #
    vr
    cv
    #
    cY
    cZ
    c.pl
    co
    wcel
    #
    wa
    #
    @7
    @9
    @11
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    @11
    cA
    wcel
    #
    @11
    vy
    cv
    #
    vz
    cv
    #
    c.or
    co
    c.le
    wbr
    #
    vz
    cZ
    wrex
    vy
    cY
    wrex
    #
    wa
    #
    @7
    cX
    cY
    c.pl
    co
    cZ
    c.pl
    co
    wcel
    #
    @16
    @12
    @22
    @10
    @12
    @8
    @14
    @6
    simpr2r
    @16
    cK
    clat
    wcel
    #
    @2
    @3
    @5
    @12
    @22
    wb
    @16
    @0
    @24
    @0
    @4
    @5
    @15
    simpl1
    cK
    hllat
    syl
    @1
    @2
    @3
    @0
    @5
    @15
    simpl22
    @1
    @2
    @3
    @0
    @5
    @15
    simpl23
    @0
    @4
    @5
    @15
    simpl3
    cA
    c.pl
    @11
    c.or
    cK
    c.le
    cY
    cZ
    vz
    vy
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    elpaddn0
    syl31anc
    mpbid
    @16
    @17
    @21
    @23
    @16
    @17
    wa
    @20
    @23
    vy
    vz
    cY
    cZ
    @16
    @17
    @18
    cY
    wcel
    #
    @19
    cZ
    wcel
    #
    wa
    #
    @20
    @23
    wi
    wi
    @16
    @17
    @27
    @20
    @23
    @6
    @15
    @17
    @27
    @20
    w3a
    #
    @23
    @6
    @15
    @28
    w3a
    #
    @0
    @4
    @8
    @17
    wa
    @10
    @25
    @26
    w3a
    @14
    @20
    wa
    @23
    @0
    @4
    @5
    @15
    @28
    simp11
    @0
    @4
    @5
    @15
    @28
    simp12
    @29
    @8
    @17
    @6
    @8
    @13
    @14
    @28
    simp21
    @6
    @15
    @17
    @27
    @20
    simp31
    jca
    @29
    @10
    @25
    @26
    @10
    @12
    @8
    @14
    @6
    @28
    simp22l
    @25
    @26
    @17
    @20
    @6
    @15
    simp32l
    @25
    @26
    @17
    @20
    @6
    @15
    simp32r
    3jca
    @29
    @14
    @20
    @6
    @8
    @13
    @14
    @28
    simp23
    @6
    @15
    @17
    @27
    @20
    simp33
    jca
    vx
    vy
    vz
    cA
    c.pl
    c.or
    cK
    c.le
    cX
    cY
    cZ
    vr
    vp
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    paddasslem14
    syl32anc
    3expia
    3expd
    imp
    rexlimdvv
    expimpd
    mpd
end
