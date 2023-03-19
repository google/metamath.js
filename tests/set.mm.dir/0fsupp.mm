include "wcel.mm"
include "c0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "supp0.mm"
include "0fin.mm"
include "syl6eqel.mm"
include "wfun.mm"
include "cvv.mm"
include "wb.mm"
include "fun0.mm"
include "0ex.mm"
include "funisfsupp.mm"
include "mp3an12.mm"
include "mpbird.mm"

theorem 0fsupp
  let cV: class V
  let cZ: class Z


  assert |- ( Z e. V -> (/) finSupp Z )

  proof
    cZ
    cV
    wcel
    #
    c0
    cZ
    cfsupp
    wbr
    #
    c0
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    @0
    @2
    c0
    cfn
    cV
    cZ
    supp0
    0fin
    syl6eqel
    c0
    wfun
    c0
    cvv
    wcel
    @0
    @1
    @3
    wb
    fun0
    0ex
    c0
    cvv
    cV
    cZ
    funisfsupp
    mp3an12
    mpbird
end
