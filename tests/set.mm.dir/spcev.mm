include "cvv.mm"
include "wcel.mm"
include "wex.mm"
include "wi.mm"
include "spcegv.mm"
include "ax-mp.mm"

theorem spcev
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume spcv.1: |- A e. _V
  assume spcv.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( ps -> E. x ph )

  proof
    cA
    cvv
    wcel
    wps
    wph
    vx
    wex
    wi
    spcv.1
    wph
    wps
    vx
    cA
    cvv
    spcv.2
    spcegv
    ax-mp
end
