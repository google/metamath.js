include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "cexp.mm"
include "co.mm"
include "expclz.mm"
include "syl3anc.mm"

theorem expclzd
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume expcld.1: |- ( ph -> A e. CC )
  assume sqrecd.1: |- ( ph -> A =/= 0 )
  assume expclzd.3: |- ( ph -> N e. ZZ )


  assert |- ( ph -> ( A ^ N ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cN
    cz
    wcel
    cA
    cN
    cexp
    co
    cc
    wcel
    expcld.1
    sqrecd.1
    expclzd.3
    cA
    cN
    expclz
    syl3anc
end
