include "rpred.mm"
include "recnd.mm"

theorem rpcnd
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> A e. CC )

  proof
    wph
    cA
    wph
    cA
    rpred.1
    rpred
    recnd
end
