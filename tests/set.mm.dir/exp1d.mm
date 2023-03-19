include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "exp1.mm"
include "syl.mm"

theorem exp1d
  let wph: wff ph
  let cA: class A
  assume expcld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A ^ 1 ) = A )

  proof
    wph
    cA
    cc
    wcel
    cA
    c1
    cexp
    co
    cA
    wceq
    expcld.1
    cA
    exp1
    syl
end
