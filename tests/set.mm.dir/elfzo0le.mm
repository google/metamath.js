include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cle.mm"
include "elfzo0.mm"
include "cr.mm"
include "wi.mm"
include "nn0re.mm"
include "nnre.mm"
include "ltle.mm"
include "syl2an.mm"
include "3impia.mm"
include "sylbi.mm"

theorem elfzo0le
  let cA: class A
  let cB: class B


  assert |- ( A e. ( 0 ..^ B ) -> A <_ B )

  proof
    cA
    cc0
    cB
    cfzo
    co
    wcel
    cA
    cn0
    wcel
    #
    cB
    cn
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    elfzo0
    @0
    @1
    @2
    @3
    @0
    cA
    cr
    wcel
    cB
    cr
    wcel
    @2
    @3
    wi
    @1
    cA
    nn0re
    cB
    nnre
    cA
    cB
    ltle
    syl2an
    3impia
    sylbi
end
