include "zred.mm"
include "recnd.mm"

theorem zcnd
  let wph: wff ph
  let cA: class A
  assume zred.1: |- ( ph -> A e. ZZ )


  assert |- ( ph -> A e. CC )

  proof
    wph
    cA
    wph
    cA
    zred.1
    zred
    recnd
end
