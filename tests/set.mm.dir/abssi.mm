include "cab.mm"
include "cv.mm"
include "wcel.mm"
include "ss2abi.mm"
include "abid2.mm"
include "sseqtri.mm"

theorem abssi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume abssi.1: |- ( ph -> x e. A )

  disjoint A x
  assert |- { x | ph } C_ A

  proof
    wph
    vx
    cab
    vx
    cv
    cA
    wcel
    #
    vx
    cab
    cA
    wph
    @0
    vx
    abssi.1
    ss2abi
    vx
    cA
    abid2
    sseqtri
end
