include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "2halves.mm"
include "syl.mm"

theorem 2halvesd
  let wph: wff ph
  let cA: class A
  assume 2timesd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( ( A / 2 ) + ( A / 2 ) ) = A )

  proof
    wph
    cA
    cc
    wcel
    cA
    c2
    cdiv
    co
    #
    @0
    caddc
    co
    cA
    wceq
    2timesd.1
    cA
    2halves
    syl
end
