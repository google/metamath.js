include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "csdm.mm"
include "wbr.mm"
include "cen.mm"
include "wn.mm"
include "php4.mm"
include "sdomnen.mm"
include "syl.mm"

theorem php5
  let cA: class A


  assert |- ( A e. _om -> -. A ~~ suc A )

  proof
    cA
    com
    wcel
    cA
    cA
    csuc
    #
    csdm
    wbr
    cA
    @0
    cen
    wbr
    wn
    cA
    php4
    cA
    @0
    sdomnen
    syl
end
