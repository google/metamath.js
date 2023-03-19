include "cvv.mm"
include "wcel.mm"
include "wex.mm"
include "wsbc.mm"
include "wb.mm"
include "nfe1.mm"
include "sbcgf.mm"
include "ax-mp.mm"

theorem sbexi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume sbexi.1: |- A e. _V


  assert |- ( [. A / x ]. E. x ph <-> E. x ph )

  proof
    cA
    cvv
    wcel
    wph
    vx
    wex
    #
    vx
    cA
    wsbc
    @0
    wb
    sbexi.1
    @0
    vx
    cA
    cvv
    wph
    vx
    nfe1
    sbcgf
    ax-mp
end
