include "cz.mm"
include "wcel.mm"
include "cneg.mm"
include "znegcl.mm"
include "syl.mm"

theorem znegcld
  let wph: wff ph
  let cA: class A
  assume zred.1: |- ( ph -> A e. ZZ )


  assert |- ( ph -> -u A e. ZZ )

  proof
    wph
    cA
    cz
    wcel
    cA
    cneg
    cz
    wcel
    zred.1
    cA
    znegcl
    syl
end
