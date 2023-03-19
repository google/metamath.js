include "cvv.mm"
include "wcel.mm"
include "wsbc.mm"
include "wb.mm"
include "sbcieg.mm"
include "ax-mp.mm"

theorem sbcie
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume sbcie.1: |- A e. _V
  assume sbcie.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( [. A / x ]. ph <-> ps )

  proof
    cA
    cvv
    wcel
    wph
    vx
    cA
    wsbc
    wps
    wb
    sbcie.1
    wph
    wps
    vx
    cA
    cvv
    sbcie.2
    sbcieg
    ax-mp
end
