include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "jca.mm"

theorem rpcnne0d
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( A e. CC /\ A =/= 0 ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    wph
    cA
    rpred.1
    rpcnd
    wph
    cA
    rpred.1
    rpne0d
    jca
end
