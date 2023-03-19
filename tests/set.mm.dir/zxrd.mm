include "zred.mm"
include "rexrd.mm"

theorem zxrd
  let wph: wff ph
  let cA: class A
  assume zxrd.1: |- ( ph -> A e. ZZ )


  assert |- ( ph -> A e. RR* )

  proof
    wph
    cA
    wph
    cA
    zxrd.1
    zred
    rexrd
end
