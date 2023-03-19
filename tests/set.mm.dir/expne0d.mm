include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "cexp.mm"
include "co.mm"
include "expne0i.mm"
include "syl3anc.mm"

theorem expne0d
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume expcld.1: |- ( ph -> A e. CC )
  assume sqrecd.1: |- ( ph -> A =/= 0 )
  assume expclzd.3: |- ( ph -> N e. ZZ )


  assert |- ( ph -> ( A ^ N ) =/= 0 )

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
    cc0
    wne
    expcld.1
    sqrecd.1
    expclzd.3
    cA
    cN
    expne0i
    syl3anc
end
