include "wcel.mm"
include "wnf.mm"
include "wsbc.mm"
include "wb.mm"
include "sbctt.mm"
include "mpan2.mm"

theorem sbcgf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume sbcgf.1: |- F/ x ph


  assert |- ( A e. V -> ( [. A / x ]. ph <-> ph ) )

  proof
    cA
    cV
    wcel
    wph
    vx
    wnf
    wph
    vx
    cA
    wsbc
    wph
    wb
    sbcgf.1
    wph
    vx
    cA
    cV
    sbctt
    mpan2
end
