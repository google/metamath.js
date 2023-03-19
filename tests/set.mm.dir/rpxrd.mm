include "rpred.mm"
include "rexrd.mm"

theorem rpxrd
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> A e. RR* )

  proof
    wph
    cA
    wph
    cA
    rpred.1
    rpred
    rexrd
end
