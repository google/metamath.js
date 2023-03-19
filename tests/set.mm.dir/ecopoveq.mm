include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "oveq12.mm"
include "eqeqan12d.mm"
include "an42s.mm"
include "opbrop.mm"

theorem ecopoveq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.sm: class .~
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vs: setvar s
  let vr: setvar r
  assume ecopopr.1: |- .~ = { <. x , y >. | ( ( x e. ( S X. S ) /\ y e. ( S X. S ) ) /\ E. z E. w E. v E. u ( ( x = <. z , w >. /\ y = <. v , u >. ) /\ ( z .+ u ) = ( w .+ v ) ) ) }

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint A w
  disjoint u v
  disjoint A v
  disjoint A u
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint C v
  disjoint C u
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint D v
  disjoint D u
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
  assert |- ( ( ( A e. S /\ B e. S ) /\ ( C e. S /\ D e. S ) ) -> ( <. A , B >. .~ <. C , D >. <-> ( A .+ D ) = ( B .+ C ) ) )

  proof
    vz
    cv
    #
    vu
    cv
    #
    c.pl
    co
    #
    vw
    cv
    #
    vv
    cv
    #
    c.pl
    co
    #
    wceq
    #
    cA
    cD
    c.pl
    co
    #
    cB
    cC
    c.pl
    co
    #
    wceq
    #
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cC
    cD
    c.sm
    cS
    @0
    cA
    wceq
    #
    @1
    cD
    wceq
    #
    @3
    cB
    wceq
    #
    @4
    cC
    wceq
    #
    @6
    @9
    wb
    @10
    @11
    wa
    @12
    @13
    wa
    @2
    @7
    @5
    @8
    @0
    cA
    @1
    cD
    c.pl
    oveq12
    @3
    cB
    @4
    cC
    c.pl
    oveq12
    eqeqan12d
    an42s
    ecopopr.1
    opbrop
end
