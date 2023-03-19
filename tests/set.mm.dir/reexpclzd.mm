include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "cexp.mm"
include "co.mm"
include "reexpclz.mm"
include "syl3anc.mm"

theorem reexpclzd
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume rpexpclzd.1: |- ( ph -> A e. RR )
  assume rpexpclzd.2: |- ( ph -> A =/= 0 )
  assume rpexpclzd.3: |- ( ph -> N e. ZZ )


  assert |- ( ph -> ( A ^ N ) e. RR )

  proof
    wph
    cA
    cr
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
    cr
    wcel
    rpexpclzd.1
    rpexpclzd.2
    rpexpclzd.3
    cA
    cN
    reexpclz
    syl3anc
end
