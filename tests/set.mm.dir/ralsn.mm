include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wral.mm"
include "wb.mm"
include "ralsng.mm"
include "ax-mp.mm"

theorem ralsn
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ralsn.1: |- A e. _V
  assume ralsn.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( A. x e. { A } ph <-> ps )

  proof
    cA
    cvv
    wcel
    wph
    vx
    cA
    csn
    wral
    wps
    wb
    ralsn.1
    wph
    wps
    vx
    cA
    cvv
    ralsn.2
    ralsng
    ax-mp
end
