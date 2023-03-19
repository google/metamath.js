include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "exp0.mm"
include "syl.mm"

theorem exp0d
  let wph: wff ph
  let cA: class A
  assume expcld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A ^ 0 ) = 1 )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    cexp
    co
    c1
    wceq
    expcld.1
    cA
    exp0
    syl
end
