include "clmod.mm"
include "wcel.mm"
include "cdr.mm"
include "wa.mm"
include "clvec.mm"
include "lmodprop2d.mm"
include "drngpropd.mm"
include "anbi12d.mm"
include "islvec.mm"
include "3bitr4g.mm"

theorem lvecprop2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  assume lvecprop2d.b1: |- ( ph -> B = ( Base ` K ) )
  assume lvecprop2d.b2: |- ( ph -> B = ( Base ` L ) )
  assume lvecprop2d.f: |- F = ( Scalar ` K )
  assume lvecprop2d.g: |- G = ( Scalar ` L )
  assume lvecprop2d.p1: |- ( ph -> P = ( Base ` F ) )
  assume lvecprop2d.p2: |- ( ph -> P = ( Base ` G ) )
  assume lvecprop2d.1: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume lvecprop2d.2: |- ( ( ph /\ ( x e. P /\ y e. P ) ) -> ( x ( +g ` F ) y ) = ( x ( +g ` G ) y ) )
  assume lvecprop2d.3: |- ( ( ph /\ ( x e. P /\ y e. P ) ) -> ( x ( .r ` F ) y ) = ( x ( .r ` G ) y ) )
  assume lvecprop2d.4: |- ( ( ph /\ ( x e. P /\ y e. B ) ) -> ( x ( .s ` K ) y ) = ( x ( .s ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint L x
  disjoint L y
  disjoint P x
  disjoint P y
  assert |- ( ph -> ( K e. LVec <-> L e. LVec ) )

  proof
    wph
    cK
    clmod
    wcel
    #
    cF
    cdr
    wcel
    #
    wa
    cL
    clmod
    wcel
    #
    cG
    cdr
    wcel
    #
    wa
    cK
    clvec
    wcel
    cL
    clvec
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
    cP
    cF
    cG
    cK
    cL
    lvecprop2d.b1
    lvecprop2d.b2
    lvecprop2d.f
    lvecprop2d.g
    lvecprop2d.p1
    lvecprop2d.p2
    lvecprop2d.1
    lvecprop2d.2
    lvecprop2d.3
    lvecprop2d.4
    lmodprop2d
    wph
    vx
    vy
    cP
    cF
    cG
    lvecprop2d.p1
    lvecprop2d.p2
    lvecprop2d.2
    lvecprop2d.3
    drngpropd
    anbi12d
    cF
    cK
    lvecprop2d.f
    islvec
    cG
    cL
    lvecprop2d.g
    islvec
    3bitr4g
end
