include "wcel.mm"
include "c0.mm"
include "cdom.mm"
include "wbr.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "cc0.mm"
include "0domg.mm"
include "hashdomi.mm"
include "hash0.mm"
include "breq1i.mm"
include "biimpi.mm"
include "3syl.mm"

theorem hashge0
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> 0 <_ ( # ` A ) )

  proof
    cA
    cV
    wcel
    c0
    cA
    cdom
    wbr
    c0
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    cle
    wbr
    #
    cc0
    @1
    cle
    wbr
    #
    cA
    cV
    0domg
    c0
    cA
    hashdomi
    @2
    @3
    @0
    cc0
    @1
    cle
    hash0
    breq1i
    biimpi
    3syl
end
