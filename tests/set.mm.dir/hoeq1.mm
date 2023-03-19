include "chil.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wb.mm"
include "ffvelrn.mm"
include "hial2eq.mm"
include "syl2an.mm"
include "anandirs.mm"
include "ralbidva.mm"
include "wfn.mm"
include "ffn.mm"
include "eqfnfv.mm"
include "bitr4d.mm"

theorem hoeq1
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let vz: setvar z
  let vu: setvar u
  let vv: setvar v

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint x z
  disjoint y z
  disjoint S z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint T u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint T v
  disjoint T z
  assert |- ( ( S : ~H --> ~H /\ T : ~H --> ~H ) -> ( A. x e. ~H A. y e. ~H ( ( S ` x ) .ih y ) = ( ( T ` x ) .ih y ) <-> S = T ) )

  proof
    chil
    chil
    cS
    wf
    #
    chil
    chil
    cT
    wf
    #
    wa
    #
    vx
    cv
    #
    cS
    cfv
    #
    vy
    cv
    #
    csp
    co
    @3
    cT
    cfv
    #
    @5
    csp
    co
    wceq
    vy
    chil
    wral
    #
    vx
    chil
    wral
    @4
    @6
    wceq
    #
    vx
    chil
    wral
    #
    cS
    cT
    wceq
    #
    @2
    @7
    @8
    vx
    chil
    @0
    @1
    @3
    chil
    wcel
    #
    @7
    @8
    wb
    #
    @0
    @11
    wa
    @4
    chil
    wcel
    @6
    chil
    wcel
    @12
    @1
    @11
    wa
    chil
    chil
    @3
    cS
    ffvelrn
    chil
    chil
    @3
    cT
    ffvelrn
    vy
    @4
    @6
    hial2eq
    syl2an
    anandirs
    ralbidva
    @0
    cS
    chil
    wfn
    cT
    chil
    wfn
    @10
    @9
    wb
    @1
    chil
    chil
    cS
    ffn
    chil
    chil
    cT
    ffn
    vx
    chil
    cS
    cT
    eqfnfv
    syl2an
    bitr4d
end
