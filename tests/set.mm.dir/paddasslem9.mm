include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "simpr31.mm"
include "jca.mm"
include "simpr1.mm"
include "simpr32.mm"
include "simpl3r.mm"
include "3jca.mm"
include "an6.mm"
include "ssel2.mm"
include "3anim123i.mm"
include "sylbi.mm"
include "3ad2antl2.mm"
include "3ad2antr1.mm"
include "simpr2l.mm"
include "simpr2r.mm"
include "simpr33.mm"
include "paddasslem7.mm"
include "syl32anc.mm"
include "paddasslem8.mm"
include "syl33anc.mm"

theorem paddasslem9
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let c.pl: class .+
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let vr: setvar r
  let vp: setvar p
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )
  assume paddasslem.p: |- .+ = ( +P ` K )


  assert |- ( ( ( K e. HL /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) /\ ( p e. A /\ r e. A ) ) /\ ( ( x e. X /\ y e. Y /\ z e. Z ) /\ ( -. r .<_ ( x .\/ y ) /\ r .<_ ( y .\/ z ) ) /\ ( s e. A /\ s .<_ ( x .\/ y ) /\ s .<_ ( p .\/ z ) ) ) ) -> p e. ( ( X .+ Y ) .+ Z ) )

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
    vp
    cv
    #
    cA
    wcel
    #
    vr
    cv
    #
    cA
    wcel
    #
    wa
    #
    w3a
    #
    vx
    cv
    #
    cX
    wcel
    #
    vy
    cv
    #
    cY
    wcel
    #
    vz
    cv
    #
    cZ
    wcel
    #
    w3a
    #
    @7
    @11
    @13
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    @7
    @13
    @15
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    vs
    cv
    #
    cA
    wcel
    #
    @22
    @18
    c.le
    wbr
    #
    @22
    @5
    @15
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    wa
    #
    @0
    @4
    @6
    @23
    wa
    @17
    @24
    @5
    @22
    @15
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
    cZ
    c.pl
    co
    wcel
    @0
    @4
    @9
    @27
    simpl1
    #
    @0
    @4
    @9
    @27
    simpl2
    @28
    @6
    @23
    @6
    @8
    @0
    @4
    @27
    simpl3l
    #
    @23
    @24
    @25
    @17
    @21
    @10
    simpr31
    #
    jca
    @10
    @17
    @21
    @26
    simpr1
    @23
    @24
    @25
    @17
    @21
    @10
    simpr32
    #
    @28
    @0
    @6
    @8
    @23
    w3a
    @11
    cA
    wcel
    #
    @13
    cA
    wcel
    #
    @15
    cA
    wcel
    #
    w3a
    #
    @19
    @20
    @24
    w3a
    @25
    @29
    @30
    @28
    @6
    @8
    @23
    @31
    @6
    @8
    @0
    @4
    @27
    simpl3r
    @32
    3jca
    @10
    @21
    @17
    @37
    @26
    @4
    @0
    @17
    @37
    @9
    @4
    @17
    wa
    @1
    @12
    wa
    #
    @2
    @14
    wa
    #
    @3
    @16
    wa
    #
    w3a
    @37
    @1
    @2
    @3
    @12
    @14
    @16
    an6
    @38
    @34
    @39
    @35
    @40
    @36
    cX
    cA
    @11
    ssel2
    cY
    cA
    @13
    ssel2
    cZ
    cA
    @15
    ssel2
    3anim123i
    sylbi
    3ad2antl2
    3ad2antr1
    @28
    @19
    @20
    @24
    @19
    @20
    @17
    @26
    @10
    simpr2l
    @19
    @20
    @17
    @26
    @10
    simpr2r
    @33
    3jca
    @23
    @24
    @25
    @17
    @21
    @10
    simpr33
    vx
    vy
    vz
    cA
    c.or
    cK
    c.le
    vs
    vr
    vp
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem7
    syl32anc
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
    vs
    vp
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    paddasslem8
    syl33anc
end
