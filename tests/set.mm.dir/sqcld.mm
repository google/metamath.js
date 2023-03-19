include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "sqcl.mm"
include "syl.mm"

theorem sqcld
  let wph: wff ph
  let cA: class A
  assume expcld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A ^ 2 ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cA
    c2
    cexp
    co
    cc
    wcel
    expcld.1
    cA
    sqcl
    syl
end
