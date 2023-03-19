include "cdrs.mm"
include "wcel.mm"
include "cpreset.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "cple.mm"
include "cfv.mm"
include "wsbc.mm"
include "cbs.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sbceq1d.mm"
include "sbceqbid.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "wb.mm"
include "neeq1.mm"
include "adantr.mm"
include "rexeq.mm"
include "raleqbi1dv.mm"
include "breq.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "2ralbidv.mm"
include "sylan9bb.mm"
include "sbc2ie.mm"
include "syl6bb.mm"
include "df-drs.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem isdrs
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
  assume isdrs.b: |- B = ( Base ` K )
  assume isdrs.l: |- .<_ = ( le ` K )

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
  assert |- ( K e. Dirset <-> ( K e. Preset /\ B =/= (/) /\ A. x e. B A. y e. B E. z e. B ( x .<_ z /\ y .<_ z ) ) )

  proof
    cK
    cdrs
    wcel
    cK
    cpreset
    wcel
    #
    cB
    c0
    wne
    #
    vx
    cv
    #
    vz
    cv
    #
    c.le
    wbr
    #
    vy
    cv
    #
    @3
    c.le
    wbr
    #
    wa
    #
    vz
    cB
    wrex
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    #
    wa
    @0
    @1
    @9
    w3a
    vb
    cv
    #
    c0
    wne
    #
    @2
    @3
    vr
    cv
    #
    wbr
    #
    @5
    @3
    @13
    wbr
    #
    wa
    #
    vz
    @11
    wrex
    #
    vy
    @11
    wral
    #
    vx
    @11
    wral
    #
    wa
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
    @21
    cbs
    cfv
    #
    wsbc
    #
    @10
    vf
    cK
    cpreset
    cdrs
    @21
    cK
    wceq
    #
    @25
    @20
    vr
    c.le
    wsbc
    #
    vb
    cB
    wsbc
    @10
    @26
    @23
    @27
    vb
    @24
    cB
    @26
    @24
    cK
    cbs
    cfv
    #
    cB
    @21
    cK
    cbs
    fveq2
    isdrs.b
    syl6eqr
    @26
    @20
    vr
    @22
    c.le
    @26
    @22
    cK
    cple
    cfv
    #
    c.le
    @21
    cK
    cple
    fveq2
    isdrs.l
    syl6eqr
    sbceq1d
    sbceqbid
    @20
    @10
    vb
    vr
    cB
    c.le
    cB
    @28
    cvv
    isdrs.b
    cK
    cbs
    fvex
    eqeltri
    c.le
    @29
    cvv
    isdrs.l
    cK
    cple
    fvex
    eqeltri
    @11
    cB
    wceq
    #
    @13
    c.le
    wceq
    #
    wa
    @12
    @1
    @19
    @9
    @30
    @12
    @1
    wb
    @31
    @11
    cB
    c0
    neeq1
    adantr
    @30
    @19
    @16
    vz
    cB
    wrex
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    @31
    @9
    @18
    @33
    vx
    @11
    cB
    @17
    @32
    vy
    @11
    cB
    @16
    vz
    @11
    cB
    rexeq
    raleqbi1dv
    raleqbi1dv
    @31
    @32
    @8
    vx
    vy
    cB
    cB
    @31
    @16
    @7
    vz
    cB
    @31
    @14
    @4
    @15
    @6
    @2
    @3
    @13
    c.le
    breq
    @5
    @3
    @13
    c.le
    breq
    anbi12d
    rexbidv
    2ralbidv
    sylan9bb
    anbi12d
    sbc2ie
    syl6bb
    vx
    vy
    vz
    vf
    vr
    vb
    df-drs
    elrab2
    @0
    @1
    @9
    3anass
    bitr4i
end
