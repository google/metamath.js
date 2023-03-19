include "cpo.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wceq.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "w3a.mm"
include "wral.mm"
include "wex.mm"
include "cbs.mm"
include "cfv.mm"
include "cple.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "3anbi12d.mm"
include "2exbidv.mm"
include "df-poset.mm"
include "elab4g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "breq.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "imbi12d.mm"
include "3anbi123d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "ceqsex2v.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem ispos
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let vb: setvar b
  let vp: setvar p
  let vr: setvar r
  assume ispos.b: |- B = ( Base ` K )
  assume ispos.l: |- .<_ = ( le ` K )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint b p
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint p r
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint B p
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint B r
  disjoint K b
  disjoint K p
  disjoint K r
  disjoint .<_ b
  disjoint .<_ p
  disjoint .<_ r
  assert |- ( K e. Poset <-> ( K e. _V /\ A. x e. B A. y e. B A. z e. B ( x .<_ x /\ ( ( x .<_ y /\ y .<_ x ) -> x = y ) /\ ( ( x .<_ y /\ y .<_ z ) -> x .<_ z ) ) ) )

  proof
    cK
    cpo
    wcel
    cK
    cvv
    wcel
    #
    vb
    cv
    #
    cB
    wceq
    #
    vr
    cv
    #
    c.le
    wceq
    #
    vx
    cv
    #
    @5
    @3
    wbr
    #
    @5
    vy
    cv
    #
    @3
    wbr
    #
    @7
    @5
    @3
    wbr
    #
    wa
    #
    @5
    @7
    wceq
    #
    wi
    #
    @8
    @7
    vz
    cv
    #
    @3
    wbr
    #
    wa
    #
    @5
    @13
    @3
    wbr
    #
    wi
    #
    w3a
    #
    vz
    @1
    wral
    #
    vy
    @1
    wral
    #
    vx
    @1
    wral
    #
    w3a
    #
    vr
    wex
    vb
    wex
    #
    wa
    @0
    @5
    @5
    c.le
    wbr
    #
    @5
    @7
    c.le
    wbr
    #
    @7
    @5
    c.le
    wbr
    #
    wa
    #
    @11
    wi
    #
    @25
    @7
    @13
    c.le
    wbr
    #
    wa
    #
    @5
    @13
    c.le
    wbr
    #
    wi
    #
    w3a
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
    wa
    @1
    vp
    cv
    #
    cbs
    cfv
    #
    wceq
    #
    @3
    @36
    cple
    cfv
    #
    wceq
    #
    @21
    w3a
    #
    vr
    wex
    vb
    wex
    @23
    vp
    cK
    cpo
    @36
    cK
    wceq
    #
    @41
    @22
    vb
    vr
    @42
    @38
    @2
    @40
    @4
    @21
    @42
    @37
    cB
    @1
    @42
    @37
    cK
    cbs
    cfv
    #
    cB
    @36
    cK
    cbs
    fveq2
    ispos.b
    syl6eqr
    eqeq2d
    @42
    @39
    c.le
    @3
    @42
    @39
    cK
    cple
    cfv
    #
    c.le
    @36
    cK
    cple
    fveq2
    ispos.l
    syl6eqr
    eqeq2d
    3anbi12d
    2exbidv
    vx
    vy
    vz
    vp
    vr
    vb
    df-poset
    elab4g
    @23
    @35
    @0
    @21
    @18
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
    @35
    vb
    vr
    cB
    c.le
    cB
    @43
    cvv
    ispos.b
    cK
    cbs
    fvex
    eqeltri
    c.le
    @44
    cvv
    ispos.l
    cK
    cple
    fvex
    eqeltri
    @20
    @46
    vx
    @1
    cB
    @19
    @45
    vy
    @1
    cB
    @18
    vz
    @1
    cB
    raleq
    raleqbi1dv
    raleqbi1dv
    @4
    @45
    @34
    vx
    vy
    cB
    cB
    @4
    @18
    @33
    vz
    cB
    @4
    @6
    @24
    @12
    @28
    @17
    @32
    @5
    @5
    @3
    c.le
    breq
    @4
    @10
    @27
    @11
    @4
    @8
    @25
    @9
    @26
    @5
    @7
    @3
    c.le
    breq
    #
    @7
    @5
    @3
    c.le
    breq
    anbi12d
    imbi1d
    @4
    @15
    @30
    @16
    @31
    @4
    @8
    @25
    @14
    @29
    @47
    @7
    @13
    @3
    c.le
    breq
    anbi12d
    @5
    @13
    @3
    c.le
    breq
    imbi12d
    3anbi123d
    ralbidv
    2ralbidv
    ceqsex2v
    anbi2i
    bitri
end
