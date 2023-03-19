include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "uzid2.mm"
include "syl.mm"

theorem uzid3
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume uzid3.1: |- Z = ( ZZ>= ` M )


  assert |- ( N e. Z -> N e. ( ZZ>= ` N ) )

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
    cN
    cuz
    cfv
    wcel
    @0
    @2
    cZ
    @1
    cN
    uzid3.1
    eleq2i
    biimpi
    cN
    cM
    uzid2
    syl
end
