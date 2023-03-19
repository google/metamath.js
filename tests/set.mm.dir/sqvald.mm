include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "sqval.mm"
include "syl.mm"

theorem sqvald
  let wph: wff ph
  let cA: class A
  assume expcld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( A ^ 2 ) = ( A x. A ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    c2
    cexp
    co
    cA
    cA
    cmul
    co
    wceq
    expcld.1
    cA
    sqval
    syl
end
