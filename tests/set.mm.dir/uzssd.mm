include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "uzss.mm"
include "syl.mm"

theorem uzssd
  let wph: wff ph
  let cM: class M
  let cN: class N
  assume uzssd.1: |- ( ph -> N e. ( ZZ>= ` M ) )


  assert |- ( ph -> ( ZZ>= ` N ) C_ ( ZZ>= ` M ) )

  proof
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    cN
    cuz
    cfv
    @0
    wss
    uzssd.1
    cM
    cN
    uzss
    syl
end
