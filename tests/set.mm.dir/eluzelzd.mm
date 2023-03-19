include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "eluzelz.mm"
include "syl.mm"

theorem eluzelzd
  let wph: wff ph
  let cM: class M
  let cN: class N
  assume eluzelzd.1: |- ( ph -> N e. ( ZZ>= ` M ) )


  assert |- ( ph -> N e. ZZ )

  proof
    wph
    cN
    cM
    cuz
    cfv
    wcel
    cN
    cz
    wcel
    eluzelzd.1
    cM
    cN
    eluzelz
    syl
end
