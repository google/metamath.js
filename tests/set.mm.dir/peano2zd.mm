include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "peano2z.mm"
include "syl.mm"

theorem peano2zd
  let wph: wff ph
  let cA: class A
  assume zred.1: |- ( ph -> A e. ZZ )


  assert |- ( ph -> ( A + 1 ) e. ZZ )

  proof
    wph
    cA
    cz
    wcel
    cA
    c1
    caddc
    co
    cz
    wcel
    zred.1
    cA
    peano2z
    syl
end
