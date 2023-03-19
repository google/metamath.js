include "cvv.mm"
include "wcel.mm"
include "wsbc.mm"
include "wb.mm"
include "sbcgf.mm"
include "ax-mp.mm"

theorem sbcgfi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume sbcgfi.1: |- A e. _V
  assume sbcgfi.2: |- F/ x ph


  assert |- ( [. A / x ]. ph <-> ph )

  proof
    cA
    cvv
    wcel
    wph
    vx
    cA
    wsbc
    wph
    wb
    sbcgfi.1
    wph
    vx
    cA
    cvv
    sbcgfi.2
    sbcgf
    ax-mp
end
