include "wcel.mm"
include "nfel1.mm"
include "wnfc.mm"
include "a1i.mm"
include "wnf.mm"
include "id.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "adantl.mm"
include "riota2df.mm"

theorem riota2f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume riota2f.1: |- F/_ x B
  assume riota2f.2: |- F/ x ps
  assume riota2f.3: |- ( x = B -> ( ph <-> ps ) )

  disjoint A x
  assert |- ( ( B e. A /\ E! x e. A ph ) -> ( ps <-> ( iota_ x e. A ph ) = B ) )

  proof
    cB
    cA
    wcel
    #
    wph
    wps
    vx
    cA
    cB
    vx
    cB
    cA
    riota2f.1
    nfel1
    vx
    cB
    wnfc
    @0
    riota2f.1
    a1i
    wps
    vx
    wnf
    @0
    riota2f.2
    a1i
    @0
    id
    vx
    cv
    cB
    wceq
    wph
    wps
    wb
    @0
    riota2f.3
    adantl
    riota2df
end
