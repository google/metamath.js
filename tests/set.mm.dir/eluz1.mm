include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "wa.mm"
include "uzval.mm"
include "eleq2d.mm"
include "breq2.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem eluz1
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( M e. ZZ -> ( N e. ( ZZ>= ` M ) <-> ( N e. ZZ /\ M <_ N ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cM
    cuz
    cfv
    #
    wcel
    cN
    cM
    vk
    cv
    #
    cle
    wbr
    #
    vk
    cz
    crab
    #
    wcel
    cN
    cz
    wcel
    cM
    cN
    cle
    wbr
    #
    wa
    @0
    @1
    @4
    cN
    vk
    cM
    uzval
    eleq2d
    @3
    @5
    vk
    cN
    cz
    @2
    cN
    cM
    cle
    breq2
    elrab
    syl6bb
end
