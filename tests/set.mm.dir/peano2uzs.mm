include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "peano2uz.mm"
include "syl6eleqr.mm"
include "eleq2s.mm"

theorem peano2uzs
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume peano2uzs.1: |- Z = ( ZZ>= ` M )


  assert |- ( N e. Z -> ( N + 1 ) e. Z )

  proof
    cN
    c1
    caddc
    co
    #
    cZ
    wcel
    cN
    cM
    cuz
    cfv
    #
    cZ
    cN
    @1
    wcel
    @0
    @1
    cZ
    cM
    cN
    peano2uz
    peano2uzs.1
    syl6eleqr
    peano2uzs.1
    eleq2s
end
