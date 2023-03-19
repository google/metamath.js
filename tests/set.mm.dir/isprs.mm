include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "cple.mm"
include "cfv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cpreset.mm"
include "wceq.mm"
include "fveq2.mm"
include "sbceq1d.mm"
include "sbceqbid.mm"
include "fvex.mm"
include "wb.mm"
include "eqtr3.mm"
include "mpan2.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "syl.mm"
include "breq.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "sylan9bb.mm"
include "sbc2ie.mm"
include "syl6bb.mm"
include "df-preset.mm"
include "elab4g.mm"

theorem isprs
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let vf: setvar f
  let vb: setvar b
  let vr: setvar r
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume isprs.b: |- B = ( Base ` K )
  assume isprs.l: |- .<_ = ( le ` K )

  disjoint K x
  disjoint K y
  disjoint K z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint K f
  disjoint K b
  disjoint K r
  disjoint b f
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint B f
  disjoint B b
  disjoint B r
  disjoint .<_ f
  disjoint .<_ b
  disjoint .<_ r
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  assert |- ( K e. Preset <-> ( K e. _V /\ A. x e. B A. y e. B A. z e. B ( x .<_ x /\ ( ( x .<_ y /\ y .<_ z ) -> x .<_ z ) ) ) )

  proof
    vx
    cv
    #
    @0
    vr
    cv
    #
    wbr
    #
    @0
    vy
    cv
    #
    @1
    wbr
    #
    @3
    vz
    cv
    #
    @1
    wbr
    #
    wa
    #
    @0
    @5
    @1
    wbr
    #
    wi
    #
    wa
    #
    vz
    vb
    cv
    #
    wral
    #
    vy
    @11
    wral
    #
    vx
    @11
    wral
    #
    vr
    vf
    cv
    #
    cple
    cfv
    #
    wsbc
    #
    vb
    @15
    cbs
    cfv
    #
    wsbc
    #
    @0
    @0
    c.le
    wbr
    #
    @0
    @3
    c.le
    wbr
    #
    @3
    @5
    c.le
    wbr
    #
    wa
    #
    @0
    @5
    c.le
    wbr
    #
    wi
    #
    wa
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    vf
    cK
    cpreset
    @15
    cK
    wceq
    #
    @19
    @14
    vr
    cK
    cple
    cfv
    #
    wsbc
    #
    vb
    cK
    cbs
    cfv
    #
    wsbc
    @28
    @29
    @17
    @31
    vb
    @18
    @32
    @15
    cK
    cbs
    fveq2
    @29
    @14
    vr
    @16
    @30
    @15
    cK
    cple
    fveq2
    sbceq1d
    sbceqbid
    @14
    @28
    vb
    vr
    @32
    @30
    cK
    cbs
    fvex
    cK
    cple
    fvex
    @11
    @32
    wceq
    #
    @14
    @10
    vz
    cB
    wral
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @1
    @30
    wceq
    #
    @28
    @33
    @11
    cB
    wceq
    #
    @14
    @36
    wb
    @33
    cB
    @32
    wceq
    @38
    isprs.b
    @11
    cB
    @32
    eqtr3
    mpan2
    @13
    @35
    vx
    @11
    cB
    @12
    @34
    vy
    @11
    cB
    @10
    vz
    @11
    cB
    raleq
    raleqbi1dv
    raleqbi1dv
    syl
    @37
    @1
    c.le
    wceq
    #
    @36
    @28
    wb
    @37
    c.le
    @30
    wceq
    @39
    isprs.l
    @1
    c.le
    @30
    eqtr3
    mpan2
    @39
    @34
    @27
    vx
    vy
    cB
    cB
    @39
    @10
    @26
    vz
    cB
    @39
    @2
    @20
    @9
    @25
    @0
    @0
    @1
    c.le
    breq
    @39
    @7
    @23
    @8
    @24
    @39
    @4
    @21
    @6
    @22
    @0
    @3
    @1
    c.le
    breq
    @3
    @5
    @1
    c.le
    breq
    anbi12d
    @0
    @5
    @1
    c.le
    breq
    imbi12d
    anbi12d
    ralbidv
    2ralbidv
    syl
    sylan9bb
    sbc2ie
    syl6bb
    vx
    vy
    vz
    vf
    vr
    vb
    df-preset
    elab4g
end
