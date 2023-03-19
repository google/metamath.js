include "cgrp.mm"
include "wcel.mm"
include "ccmn.mm"
include "wa.mm"
include "cabl.mm"
include "grppropd.mm"
include "cmnpropd.mm"
include "anbi12d.mm"
include "isabl.mm"
include "3bitr4g.mm"

theorem ablpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vu: setvar u
  let vv: setvar v
  assume ablpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume ablpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume ablpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint K u
  disjoint K v
  disjoint L u
  disjoint L v
  disjoint ph u
  disjoint ph v
  assert |- ( ph -> ( K e. Abel <-> L e. Abel ) )

  proof
    wph
    cK
    cgrp
    wcel
    #
    cK
    ccmn
    wcel
    #
    wa
    cL
    cgrp
    wcel
    #
    cL
    ccmn
    wcel
    #
    wa
    cK
    cabl
    wcel
    cL
    cabl
    wcel
    wph
    @0
    @2
    @1
    @3
    wph
    vx
    vy
    cB
    cK
    cL
    ablpropd.1
    ablpropd.2
    ablpropd.3
    grppropd
    wph
    vx
    vy
    cB
    cK
    cL
    ablpropd.1
    ablpropd.2
    ablpropd.3
    cmnpropd
    anbi12d
    cK
    isabl
    cL
    isabl
    3bitr4g
end
