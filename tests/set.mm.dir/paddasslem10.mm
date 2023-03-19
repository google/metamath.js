include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wrex.mm"
include "simpl11.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "3jca.mm"
include "an6.mm"
include "ssel2.mm"
include "3anim123i.mm"
include "sylbi.mm"
include "3ad2antl2.mm"
include "adantrr.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simprr1.mm"
include "simprr2.mm"
include "simprr3.mm"
include "paddasslem4.mm"
include "syl32anc.mm"
include "simpl2.mm"
include "simpl3.mm"
include "adantr.mm"
include "simplrl.mm"
include "jca.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "paddasslem9.mm"
include "syl13anc.mm"
include "rexlimddv.mm"

theorem paddasslem10
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
  let vr: setvar r
  let vp: setvar p
  let vs: setvar s
  assume paddasslem.l: |- .<_ = ( le ` K )
  assume paddasslem.j: |- .\/ = ( join ` K )
  assume paddasslem.a: |- A = ( Atoms ` K )
  assume paddasslem.p: |- .+ = ( +P ` K )


  assert |- ( ( ( ( K e. HL /\ p =/= z /\ x =/= y ) /\ ( X C_ A /\ Y C_ A /\ Z C_ A ) /\ ( p e. A /\ r e. A ) ) /\ ( ( x e. X /\ y e. Y /\ z e. Z ) /\ ( -. r .<_ ( x .\/ y ) /\ p .<_ ( x .\/ r ) /\ r .<_ ( y .\/ z ) ) ) ) -> p e. ( ( X .+ Y ) .+ Z ) )

  proof
    cK
    chlt
    wcel
    #
    vp
    cv
    #
    vz
    cv
    #
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    w3a
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
    @1
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
    @4
    cX
    wcel
    #
    @5
    cY
    wcel
    #
    @2
    cZ
    wcel
    #
    w3a
    #
    @13
    @4
    @5
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    @1
    @4
    @13
    c.or
    co
    c.le
    wbr
    #
    @13
    @5
    @2
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    wa
    #
    vs
    cv
    #
    @21
    c.le
    wbr
    #
    @28
    @1
    @2
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    @1
    cX
    cY
    c.pl
    co
    cZ
    c.pl
    co
    wcel
    #
    vs
    cA
    @27
    @0
    @12
    @14
    w3a
    @4
    cA
    wcel
    #
    @5
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    w3a
    #
    @3
    @6
    @22
    w3a
    @23
    @24
    @31
    vs
    cA
    wrex
    @27
    @0
    @12
    @14
    @0
    @3
    @6
    @11
    @15
    @26
    simpl11
    #
    @12
    @14
    @7
    @11
    @26
    simpl3l
    @12
    @14
    @7
    @11
    @26
    simpl3r
    3jca
    @16
    @20
    @36
    @25
    @11
    @7
    @20
    @36
    @15
    @11
    @20
    wa
    @8
    @17
    wa
    #
    @9
    @18
    wa
    #
    @10
    @19
    wa
    #
    w3a
    @36
    @8
    @9
    @10
    @17
    @18
    @19
    an6
    @38
    @33
    @39
    @34
    @40
    @35
    cX
    cA
    @4
    ssel2
    cY
    cA
    @5
    ssel2
    cZ
    cA
    @2
    ssel2
    3anim123i
    sylbi
    3ad2antl2
    adantrr
    @27
    @3
    @6
    @22
    @0
    @3
    @6
    @11
    @15
    @26
    simpl12
    @0
    @3
    @6
    @11
    @15
    @26
    simpl13
    @22
    @23
    @24
    @20
    @16
    simprr1
    #
    3jca
    @22
    @23
    @24
    @20
    @16
    simprr2
    @22
    @23
    @24
    @20
    @16
    simprr3
    #
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
    paddasslem4
    syl32anc
    @27
    @28
    cA
    wcel
    #
    @31
    wa
    #
    wa
    #
    @0
    @11
    @15
    w3a
    #
    @20
    @22
    @24
    wa
    #
    @43
    @29
    @30
    w3a
    @32
    @27
    @46
    @44
    @27
    @0
    @11
    @15
    @37
    @7
    @11
    @15
    @26
    simpl2
    @7
    @11
    @15
    @26
    simpl3
    3jca
    adantr
    @16
    @20
    @25
    @44
    simplrl
    @27
    @47
    @44
    @27
    @22
    @24
    @41
    @42
    jca
    adantr
    @45
    @43
    @29
    @30
    @27
    @43
    @31
    simprl
    @27
    @43
    @29
    @30
    simprrl
    @27
    @43
    @29
    @30
    simprrr
    3jca
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
    vr
    vp
    paddasslem.l
    paddasslem.j
    paddasslem.a
    paddasslem.p
    paddasslem9
    syl13anc
    rexlimddv
end
