include "cvv.mm"
include "wcel.mm"
include "cab.mm"
include "wb.mm"
include "nfcv.mm"
include "elabgf.mm"
include "ax-mp.mm"

theorem elabf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume elabf.1: |- F/ x ps
  assume elabf.2: |- A e. _V
  assume elabf.3: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  assert |- ( A e. { x | ph } <-> ps )

  proof
    cA
    cvv
    wcel
    cA
    wph
    vx
    cab
    wcel
    wps
    wb
    elabf.2
    wph
    wps
    vx
    cA
    cvv
    vx
    cA
    nfcv
    elabf.1
    elabf.3
    elabgf
    ax-mp
end
