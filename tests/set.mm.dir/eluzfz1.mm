include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "cz.mm"
include "eluzel2.mm"
include "uzid.mm"
include "syl.mm"
include "eluzfz.mm"
include "mpancom.mm"

theorem eluzfz1
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> M e. ( M ... N ) )

  proof
    cM
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    @0
    wcel
    #
    cM
    cM
    cN
    cfz
    co
    wcel
    @2
    cM
    cz
    wcel
    @1
    cM
    cN
    eluzel2
    cM
    uzid
    syl
    cM
    cM
    cN
    eluzfz
    mpancom
end
