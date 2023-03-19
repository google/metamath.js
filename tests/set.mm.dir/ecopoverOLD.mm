include "cxp.mm"
include "wer.mm"
include "wtru.mm"
include "wrel.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "co.mm"
include "wex.mm"
include "relopabi.mm"
include "a1i.mm"
include "wbr.mm"
include "ecopovsym.mm"
include "adantl.mm"
include "ecopovtrn.mm"
include "wi.mm"
include "wral.mm"
include "vex.mm"
include "caovcom.mm"
include "ecopoveq.mm"
include "mpbiri.mm"
include "anidms.mm"
include "rgen2a.mm"
include "wb.mm"
include "breq12.mm"
include "ralxp.mm"
include "mpbir.mm"
include "rspec.mm"
include "copab.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "ssbri.mm"
include "brxp.mm"
include "simplbi.mm"
include "syl.mm"
include "impbid1.mm"
include "iserd.mm"
include "trud.mm"

theorem ecopoverOLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let c.pl: class .+
  let c.sm: class .~
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vs: setvar s
  let vr: setvar r
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ecopopr.1: |- .~ = { <. x , y >. | ( ( x e. ( S X. S ) /\ y e. ( S X. S ) ) /\ E. z E. w E. v E. u ( ( x = <. z , w >. /\ y = <. v , u >. ) /\ ( z .+ u ) = ( w .+ v ) ) ) }
  assume ecopopr.com: |- ( x .+ y ) = ( y .+ x )
  assume ecopopr.cl: |- ( ( x e. S /\ y e. S ) -> ( x .+ y ) e. S )
  assume ecopopr.ass: |- ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) )
  assume ecopopr.can: |- ( ( x e. S /\ y e. S ) -> ( ( x .+ y ) = ( x .+ z ) -> y = z ) )

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
  assert |- .~ Er ( S X. S )

  proof
    cS
    cS
    cxp
    #
    c.sm
    wer
    wtru
    vf
    vg
    vh
    @0
    c.sm
    c.sm
    wrel
    wtru
    vx
    cv
    #
    @0
    wcel
    vy
    cv
    #
    @0
    wcel
    wa
    @1
    vz
    cv
    #
    vw
    cv
    #
    cop
    wceq
    @2
    vv
    cv
    #
    vu
    cv
    #
    cop
    wceq
    wa
    @3
    @6
    c.pl
    co
    @4
    @5
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
    #
    vx
    vy
    c.sm
    ecopopr.1
    relopabi
    a1i
    vf
    cv
    #
    vg
    cv
    #
    c.sm
    wbr
    #
    @10
    @9
    c.sm
    wbr
    wtru
    vx
    vy
    vz
    vw
    vv
    vu
    @9
    @10
    c.pl
    c.sm
    cS
    ecopopr.1
    ecopopr.com
    ecopovsym
    adantl
    @11
    @10
    vh
    cv
    #
    c.sm
    wbr
    wa
    @9
    @12
    c.sm
    wbr
    wtru
    vx
    vy
    vz
    vw
    vv
    vu
    @9
    @10
    @12
    c.pl
    c.sm
    cS
    ecopopr.1
    ecopopr.com
    ecopopr.cl
    ecopopr.ass
    ecopopr.can
    ecopovtrn
    adantl
    wtru
    @9
    @0
    wcel
    #
    @9
    @9
    c.sm
    wbr
    #
    @13
    @14
    wi
    wtru
    @14
    vf
    @0
    @14
    vf
    @0
    wral
    @10
    @12
    cop
    #
    @15
    c.sm
    wbr
    #
    vh
    cS
    wral
    vg
    cS
    wral
    @16
    vg
    vh
    cS
    @10
    cS
    wcel
    @12
    cS
    wcel
    wa
    #
    @16
    @17
    @17
    wa
    @16
    @10
    @12
    c.pl
    co
    @12
    @10
    c.pl
    co
    wceq
    vx
    vy
    @10
    @12
    c.pl
    vg
    vex
    vh
    vex
    ecopopr.com
    caovcom
    vx
    vy
    vz
    vw
    vv
    vu
    @10
    @12
    @10
    @12
    c.pl
    c.sm
    cS
    ecopopr.1
    ecopoveq
    mpbiri
    anidms
    rgen2a
    @14
    @16
    vf
    vg
    vh
    cS
    cS
    @9
    @15
    wceq
    @14
    @16
    wb
    @9
    @15
    @9
    @15
    c.sm
    breq12
    anidms
    ralxp
    mpbir
    rspec
    a1i
    @14
    @9
    @9
    @0
    @0
    cxp
    #
    wbr
    #
    @13
    c.sm
    @18
    @9
    @9
    c.sm
    @8
    vx
    vy
    copab
    @18
    ecopopr.1
    @7
    vx
    vy
    @0
    @0
    opabssxp
    eqsstri
    ssbri
    @19
    @13
    @13
    @9
    @9
    @0
    @0
    brxp
    simplbi
    syl
    impbid1
    iserd
    trud
end
