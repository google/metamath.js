include "wbr.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "co.mm"
include "wex.mm"
include "copab.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "brel.mm"
include "eqid.mm"
include "breq1.mm"
include "breq2.mm"
include "bibi12d.mm"
include "ecopoveq.mm"
include "vex.mm"
include "caovcom.mm"
include "eqeq12i.mm"
include "eqcom.mm"
include "bitri.mm"
include "syl6bb.mm"
include "ancoms.mm"
include "bitr4d.mm"
include "2optocl.mm"
include "syl.mm"
include "ibi.mm"

theorem ecopovsym
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.sm: class .~
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vs: setvar s
  let vr: setvar r
  let cC: class C
  let cD: class D
  assume ecopopr.1: |- .~ = { <. x , y >. | ( ( x e. ( S X. S ) /\ y e. ( S X. S ) ) /\ E. z E. w E. v E. u ( ( x = <. z , w >. /\ y = <. v , u >. ) /\ ( z .+ u ) = ( w .+ v ) ) ) }
  assume ecopopr.com: |- ( x .+ y ) = ( y .+ x )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint .+ x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint .+ y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint .+ z
  disjoint v w
  disjoint u w
  disjoint .+ w
  disjoint u v
  disjoint .+ v
  disjoint .+ u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint S w
  disjoint S v
  disjoint S u
  disjoint f g
  disjoint f h
  disjoint f t
  disjoint f s
  disjoint f r
  disjoint A f
  disjoint g h
  disjoint g t
  disjoint g s
  disjoint g r
  disjoint A g
  disjoint h t
  disjoint h s
  disjoint h r
  disjoint A h
  disjoint s t
  disjoint r t
  disjoint A t
  disjoint r s
  disjoint A s
  disjoint A r
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B t
  disjoint B s
  disjoint B r
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C t
  disjoint C s
  disjoint C r
  disjoint D f
  disjoint D g
  disjoint D h
  disjoint D t
  disjoint D s
  disjoint D r
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint t x
  disjoint s x
  disjoint r x
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint t y
  disjoint s y
  disjoint r y
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint t z
  disjoint s z
  disjoint r z
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint t w
  disjoint s w
  disjoint r w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint t v
  disjoint s v
  disjoint r v
  disjoint f u
  disjoint g u
  disjoint h u
  disjoint t u
  disjoint s u
  disjoint r u
  disjoint .+ f
  disjoint .+ g
  disjoint .+ h
  disjoint .+ t
  disjoint .+ s
  disjoint .+ r
  disjoint .~ f
  disjoint .~ g
  disjoint .~ h
  disjoint .~ t
  disjoint .~ s
  disjoint .~ r
  disjoint S f
  disjoint S g
  disjoint S h
  disjoint S t
  disjoint S s
  disjoint S r
  assert |- ( A .~ B -> B .~ A )

  proof
    cA
    cB
    c.sm
    wbr
    #
    cB
    cA
    c.sm
    wbr
    #
    @0
    cA
    cS
    cS
    cxp
    #
    wcel
    cB
    @2
    wcel
    wa
    @0
    @1
    wb
    #
    cA
    cB
    @2
    @2
    c.sm
    c.sm
    vx
    cv
    #
    @2
    wcel
    vy
    cv
    #
    @2
    wcel
    wa
    @4
    vz
    cv
    #
    vw
    cv
    #
    cop
    wceq
    @5
    vv
    cv
    #
    vu
    cv
    #
    cop
    wceq
    wa
    @6
    @9
    c.pl
    co
    @7
    @8
    c.pl
    co
    wceq
    wa
    vu
    wex
    vv
    wex
    vw
    wex
    vz
    wex
    #
    wa
    vx
    vy
    copab
    @2
    @2
    cxp
    ecopopr.1
    @10
    vx
    vy
    @2
    @2
    opabssxp
    eqsstri
    brel
    vf
    cv
    #
    vg
    cv
    #
    cop
    #
    vh
    cv
    #
    vt
    cv
    #
    cop
    #
    c.sm
    wbr
    #
    @16
    @13
    c.sm
    wbr
    #
    wb
    cA
    @16
    c.sm
    wbr
    #
    @16
    cA
    c.sm
    wbr
    #
    wb
    @3
    vf
    vg
    vh
    vt
    cA
    cB
    cS
    cS
    @2
    @2
    eqid
    @13
    cA
    wceq
    @17
    @19
    @18
    @20
    @13
    cA
    @16
    c.sm
    breq1
    @13
    cA
    @16
    c.sm
    breq2
    bibi12d
    @16
    cB
    wceq
    @19
    @0
    @20
    @1
    @16
    cB
    cA
    c.sm
    breq2
    @16
    cB
    cA
    c.sm
    breq1
    bibi12d
    @11
    cS
    wcel
    @12
    cS
    wcel
    wa
    #
    @14
    cS
    wcel
    @15
    cS
    wcel
    wa
    #
    wa
    #
    @17
    @14
    @12
    c.pl
    co
    #
    @15
    @11
    c.pl
    co
    #
    wceq
    #
    @18
    @23
    @17
    @11
    @15
    c.pl
    co
    #
    @12
    @14
    c.pl
    co
    #
    wceq
    #
    @26
    vx
    vy
    vz
    vw
    vv
    vu
    @11
    @12
    @14
    @15
    c.pl
    c.sm
    cS
    ecopopr.1
    ecopoveq
    @29
    @25
    @24
    wceq
    @26
    @27
    @25
    @28
    @24
    vx
    vy
    @11
    @15
    c.pl
    vf
    vex
    vt
    vex
    ecopopr.com
    caovcom
    vx
    vy
    @12
    @14
    c.pl
    vg
    vex
    vh
    vex
    ecopopr.com
    caovcom
    eqeq12i
    @25
    @24
    eqcom
    bitri
    syl6bb
    @22
    @21
    @18
    @26
    wb
    vx
    vy
    vz
    vw
    vv
    vu
    @14
    @15
    @11
    @12
    c.pl
    c.sm
    cS
    ecopopr.1
    ecopoveq
    ancoms
    bitr4d
    2optocl
    syl
    ibi
end
