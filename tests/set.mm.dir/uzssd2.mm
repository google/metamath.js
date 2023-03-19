include "cuz.mm"
include "cfv.mm"
include "syl6eleq.mm"
include "uzssd.mm"
include "syl6sseqr.mm"

theorem uzssd2
  let wph: wff ph
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume uzssd2.1: |- Z = ( ZZ>= ` M )
  assume uzssd2.2: |- ( ph -> N e. Z )


  assert |- ( ph -> ( ZZ>= ` N ) C_ Z )

  proof
    wph
    cN
    cuz
    cfv
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cN
    wph
    cN
    cZ
    @0
    uzssd2.2
    uzssd2.1
    syl6eleq
    uzssd
    uzssd2.1
    syl6sseqr
end
