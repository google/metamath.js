include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wne.mm"
include "w3a.mm"
include "wrex.mm"
include "lhpexle2.mm"
include "3anass.mm"
include "rexbii.mm"
include "sylib.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "simpl1.mm"
include "simpl3l.mm"
include "simpl2l.mm"
include "simprl.mm"
include "simpl3r.mm"
include "simpl2r.mm"
include "simprr.mm"
include "lhpexle3lem.mm"
include "syl133anc.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "lhpexle1lem.mm"
include "an31.mm"
include "3bitr4i.mm"
include "3expa.mm"
include "an32.mm"

theorem lhpexle3
  let cA: class A
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  assume lhpex1.l: |- .<_ = ( le ` K )
  assume lhpex1.a: |- A = ( Atoms ` K )
  assume lhpex1.h: |- H = ( LHyp ` K )

  disjoint .<_ p
  disjoint A p
  disjoint H p
  disjoint K p
  disjoint W p
  disjoint X p
  disjoint Y p
  disjoint Z p
  assert |- ( ( K e. HL /\ W e. H ) -> E. p e. A ( p .<_ W /\ ( p =/= X /\ p =/= Y /\ p =/= Z ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    #
    @1
    cX
    wne
    #
    @1
    cY
    wne
    #
    wa
    #
    @1
    cZ
    wne
    #
    w3a
    #
    vp
    cA
    wrex
    #
    @2
    @3
    @4
    @6
    w3a
    #
    wa
    #
    vp
    cA
    wrex
    @0
    @5
    cA
    c.le
    cW
    cZ
    vp
    @0
    @2
    @3
    @4
    w3a
    #
    vp
    cA
    wrex
    @2
    @5
    wa
    #
    vp
    cA
    wrex
    cA
    cH
    cK
    c.le
    cW
    cX
    cY
    vp
    lhpex1.l
    lhpex1.a
    lhpex1.h
    lhpexle2
    @11
    @12
    vp
    cA
    @2
    @3
    @4
    3anass
    rexbii
    sylib
    @0
    cZ
    cA
    wcel
    #
    cZ
    cW
    c.le
    wbr
    #
    wa
    #
    wa
    #
    @2
    @3
    @6
    wa
    #
    @4
    w3a
    #
    vp
    cA
    wrex
    #
    @8
    @16
    @17
    cA
    c.le
    cW
    cY
    vp
    @16
    @2
    @3
    @6
    w3a
    #
    vp
    cA
    wrex
    #
    @2
    @17
    wa
    #
    vp
    cA
    wrex
    @0
    @21
    @15
    cA
    cH
    cK
    c.le
    cW
    cX
    cZ
    vp
    lhpex1.l
    lhpex1.a
    lhpex1.h
    lhpexle2
    adantr
    @20
    @22
    vp
    cA
    @2
    @3
    @6
    3anass
    rexbii
    sylib
    @0
    @15
    cY
    cA
    wcel
    #
    cY
    cW
    c.le
    wbr
    #
    wa
    #
    @19
    @0
    @15
    @25
    w3a
    #
    @2
    @4
    @6
    wa
    #
    @3
    w3a
    #
    vp
    cA
    wrex
    #
    @19
    @26
    @27
    cA
    c.le
    cW
    cX
    vp
    @0
    @15
    @2
    @27
    wa
    #
    vp
    cA
    wrex
    #
    @25
    @0
    @2
    @4
    @6
    w3a
    #
    vp
    cA
    wrex
    @31
    cA
    cH
    cK
    c.le
    cW
    cY
    cZ
    vp
    lhpex1.l
    lhpex1.a
    lhpex1.h
    lhpexle2
    @32
    @30
    vp
    cA
    @2
    @4
    @6
    3anass
    rexbii
    sylib
    3ad2ant1
    @26
    cX
    cA
    wcel
    #
    cX
    cW
    c.le
    wbr
    #
    wa
    #
    wa
    #
    @2
    @4
    @6
    @3
    w3a
    #
    wa
    #
    vp
    cA
    wrex
    #
    @29
    @36
    @0
    @23
    @13
    @33
    @24
    @14
    @34
    @39
    @0
    @15
    @25
    @35
    simpl1
    @23
    @24
    @0
    @15
    @35
    simpl3l
    @13
    @14
    @0
    @25
    @35
    simpl2l
    @26
    @33
    @34
    simprl
    @23
    @24
    @0
    @15
    @35
    simpl3r
    @13
    @14
    @0
    @25
    @35
    simpl2r
    @26
    @33
    @34
    simprr
    cA
    cH
    cK
    c.le
    cW
    cY
    cZ
    cX
    vp
    lhpex1.l
    lhpex1.a
    lhpex1.h
    lhpexle3lem
    syl133anc
    @38
    @28
    vp
    cA
    @38
    @2
    @27
    @3
    wa
    #
    wa
    #
    @28
    @37
    @40
    @2
    @4
    @6
    @3
    df-3an
    anbi2i
    @2
    @27
    @3
    3anass
    #
    bitr4i
    rexbii
    sylib
    lhpexle1lem
    @28
    @18
    vp
    cA
    @41
    @2
    @17
    @4
    wa
    #
    wa
    #
    @28
    @18
    @40
    @43
    @2
    @4
    @6
    @3
    an31
    anbi2i
    @42
    @2
    @17
    @4
    3anass
    #
    3bitr4i
    rexbii
    sylib
    3expa
    lhpexle1lem
    @18
    @7
    vp
    cA
    @44
    @2
    @5
    @6
    wa
    #
    wa
    #
    @18
    @7
    @43
    @46
    @2
    @3
    @6
    @4
    an32
    anbi2i
    @45
    @2
    @5
    @6
    3anass
    #
    3bitr4i
    rexbii
    sylib
    lhpexle1lem
    @7
    @10
    vp
    cA
    @7
    @47
    @10
    @48
    @9
    @46
    @2
    @3
    @4
    @6
    df-3an
    anbi2i
    bitr4i
    rexbii
    sylib
end
