include "cv.mm"
include "wcel.mm"
include "wif.mm"
include "cif.mm"
include "bj-df-ifc.mm"
include "abeq2i.mm"

theorem bj-ififc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint ph x
  disjoint A x
  disjoint B x
  assert |- ( x e. if ( ph , A , B ) <-> if- ( ph , x e. A , x e. B ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wif
    vx
    wph
    cA
    cB
    cif
    wph
    vx
    cA
    cB
    bj-df-ifc
    abeq2i
end
