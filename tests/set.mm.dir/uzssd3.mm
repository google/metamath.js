include "wcel.mm"
include "id.mm"
include "uzssd2.mm"

theorem uzssd3
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume uzssd3.1: |- Z = ( ZZ>= ` M )


  assert |- ( N e. Z -> ( ZZ>= ` N ) C_ Z )

  proof
    cN
    cZ
    wcel
    #
    cM
    cN
    cZ
    uzssd3.1
    @0
    id
    uzssd2
end
