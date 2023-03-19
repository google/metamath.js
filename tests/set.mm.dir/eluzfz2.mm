include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "cz.mm"
include "eluzelz.mm"
include "uzid.mm"
include "syl.mm"
include "eluzfz.mm"
include "mpdan.mm"

theorem eluzfz2
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> N e. ( M ... N ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cN
    cN
    cuz
    cfv
    wcel
    #
    cN
    cM
    cN
    cfz
    co
    wcel
    @0
    cN
    cz
    wcel
    @1
    cM
    cN
    eluzelz
    cN
    uzid
    syl
    cN
    cM
    cN
    eluzfz
    mpdan
end
