include "cen.mm"
include "wbr.mm"
include "ensym.mm"
include "syl.mm"

theorem ensymd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ensymd.1: |- ( ph -> A ~~ B )


  assert |- ( ph -> B ~~ A )

  proof
    wph
    cA
    cB
    cen
    wbr
    cB
    cA
    cen
    wbr
    ensymd.1
    cA
    cB
    ensym
    syl
end
