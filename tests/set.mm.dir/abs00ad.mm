include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "abs00.mm"
include "syl.mm"

theorem abs00ad
  let wph: wff ph
  let cA: class A
  assume abs00ad.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( ( abs ` A ) = 0 <-> A = 0 ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cabs
    cfv
    cc0
    wceq
    cA
    cc0
    wceq
    wb
    abs00ad.1
    cA
    abs00
    syl
end
