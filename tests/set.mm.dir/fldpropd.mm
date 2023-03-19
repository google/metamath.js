include "cdr.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cfield.mm"
include "drngpropd.mm"
include "crngpropd.mm"
include "anbi12d.mm"
include "isfld.mm"
include "3bitr4g.mm"

theorem fldpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  assume drngpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume drngpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume drngpropd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume drngpropd.4: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint L x
  disjoint L y
  assert |- ( ph -> ( K e. Field <-> L e. Field ) )

  proof
    wph
    cK
    cdr
    wcel
    #
    cK
    ccrg
    wcel
    #
    wa
    cL
    cdr
    wcel
    #
    cL
    ccrg
    wcel
    #
    wa
    cK
    cfield
    wcel
    cL
    cfield
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
    drngpropd.1
    drngpropd.2
    drngpropd.3
    drngpropd.4
    drngpropd
    wph
    vx
    vy
    cB
    cK
    cL
    drngpropd.1
    drngpropd.2
    drngpropd.3
    drngpropd.4
    crngpropd
    anbi12d
    cK
    isfld
    cL
    isfld
    3bitr4g
end
