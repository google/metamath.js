include "cvv.mm"
include "wcel.mm"
include "wal.mm"
include "wsbc.mm"
include "wb.mm"
include "nfa1.mm"
include "sbcgf.mm"
include "ax-mp.mm"

theorem sbali
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume sbali.1: |- A e. _V


  assert |- ( [. A / x ]. A. x ph <-> A. x ph )

  proof
    cA
    cvv
    wcel
    wph
    vx
    wal
    #
    vx
    cA
    wsbc
    @0
    wb
    sbali.1
    @0
    vx
    cA
    cvv
    wph
    vx
    nfa1
    sbcgf
    ax-mp
end
