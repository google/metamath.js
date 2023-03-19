include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eluzelz.mm"
include "syl.mm"

theorem eluzelz2
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume eluzelz2.1: |- Z = ( ZZ>= ` M )


  assert |- ( N e. Z -> N e. ZZ )

  proof
    cN
    cZ
    wcel
    #
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    @0
    @2
    cZ
    @1
    cN
    eluzelz2.1
    eleq2i
    biimpi
    cM
    cN
    eluzelz
    syl
end
