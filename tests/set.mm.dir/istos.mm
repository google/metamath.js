include "cv.mm"
include "wbr.mm"
include "wo.mm"
include "wral.mm"
include "cple.mm"
include "cfv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cpo.mm"
include "ctos.mm"
include "wceq.mm"
include "fveq2.mm"
include "sbceq1d.mm"
include "sbceqbid.mm"
include "fvex.mm"
include "wb.mm"
include "wi.mm"
include "wa.mm"
include "eqtr.mm"
include "breq.mm"
include "orbi12d.mm"
include "2ralbidv.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "sylan9bb.mm"
include "ex.mm"
include "syl.mm"
include "expcom.mm"
include "eqcoms.mm"
include "ax-mp.mm"
include "syl5com.mm"
include "imp.mm"
include "sbc2ie.mm"
include "syl6bb.mm"
include "df-toset.mm"
include "elrab2.mm"

theorem istos
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let vb: setvar b
  let vf: setvar f
  let vr: setvar r
  assume istos.b: |- B = ( Base ` K )
  assume istos.l: |- .<_ = ( le ` K )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint .<_ x
  disjoint .<_ y
  disjoint b f
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint r x
  disjoint r y
  disjoint B r
  disjoint K b
  disjoint K f
  disjoint K r
  disjoint .<_ b
  disjoint .<_ f
  disjoint .<_ r
  assert |- ( K e. Toset <-> ( K e. Poset /\ A. x e. B A. y e. B ( x .<_ y \/ y .<_ x ) ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vr
    cv
    #
    wbr
    #
    @1
    @0
    @2
    wbr
    #
    wo
    #
    vy
    vb
    cv
    #
    wral
    vx
    @6
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
    @8
    cbs
    cfv
    #
    wsbc
    #
    @0
    @1
    c.le
    wbr
    #
    @1
    @0
    c.le
    wbr
    #
    wo
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    vf
    cK
    cpo
    ctos
    @8
    cK
    wceq
    #
    @12
    @7
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
    @17
    @18
    @10
    @20
    vb
    @11
    @21
    @8
    cK
    cbs
    fveq2
    @18
    @7
    vr
    @9
    @19
    @8
    cK
    cple
    fveq2
    sbceq1d
    sbceqbid
    @7
    @17
    vb
    vr
    @21
    @19
    cK
    cbs
    fvex
    cK
    cple
    fvex
    @6
    @21
    wceq
    #
    @2
    @19
    wceq
    #
    @7
    @17
    wb
    #
    cB
    @21
    wceq
    @22
    @23
    @24
    wi
    #
    wi
    #
    istos.b
    @26
    @21
    cB
    @22
    @21
    cB
    wceq
    #
    @25
    @22
    @27
    wa
    @6
    cB
    wceq
    #
    @23
    @24
    @6
    @21
    cB
    eqtr
    c.le
    @19
    wceq
    @23
    @28
    @24
    wi
    #
    wi
    #
    istos.l
    @30
    @19
    c.le
    @23
    @19
    c.le
    wceq
    #
    @29
    @23
    @31
    wa
    @2
    c.le
    wceq
    #
    @29
    @2
    @19
    c.le
    eqtr
    @32
    @28
    @24
    @32
    @7
    @15
    vy
    @6
    wral
    #
    vx
    @6
    wral
    @28
    @17
    @32
    @5
    @15
    vx
    vy
    @6
    @6
    @32
    @3
    @13
    @4
    @14
    @0
    @1
    @2
    c.le
    breq
    @1
    @0
    @2
    c.le
    breq
    orbi12d
    2ralbidv
    @33
    @16
    vx
    @6
    cB
    @15
    vy
    @6
    cB
    raleq
    raleqbi1dv
    sylan9bb
    ex
    syl
    expcom
    eqcoms
    ax-mp
    syl5com
    expcom
    eqcoms
    ax-mp
    imp
    sbc2ie
    syl6bb
    vx
    vy
    vf
    vr
    vb
    df-toset
    elrab2
end
