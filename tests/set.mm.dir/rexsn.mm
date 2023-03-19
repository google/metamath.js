include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wrex.mm"
include "wb.mm"
include "rexsng.mm"
include "ax-mp.mm"

theorem rexsn
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ralsn.1: |- A e. _V
  assume ralsn.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( E. x e. { A } ph <-> ps )

  proof
    cA
    cvv
    wcel
    wph
    vx
    cA
    csn
    wrex
    wps
    wb
    ralsn.1
    wph
    wps
    vx
    cA
    cvv
    ralsn.2
    rexsng
    ax-mp
end
