include "cvv.mm"
include "wcel.mm"
include "wal.mm"
include "wi.mm"
include "spcgv.mm"
include "ax-mp.mm"

theorem spcv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume spcv.1: |- A e. _V
  assume spcv.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( A. x ph -> ps )

  proof
    cA
    cvv
    wcel
    wph
    vx
    wal
    wps
    wi
    spcv.1
    wph
    wps
    vx
    cA
    cvv
    spcv.2
    spcgv
    ax-mp
end
