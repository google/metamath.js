include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cr.mm"
include "wf.mm"
include "cn.mm"
include "wb.mm"
include "eleenn.mm"
include "elee.mm"
include "syl.mm"
include "ibi.mm"

theorem eleei
  let cA: class A
  let cN: class N


  assert |- ( A e. ( EE ` N ) -> A : ( 1 ... N ) --> RR )

  proof
    cA
    cN
    cee
    cfv
    wcel
    #
    c1
    cN
    cfz
    co
    cr
    cA
    wf
    #
    @0
    cN
    cn
    wcel
    @0
    @1
    wb
    cA
    cN
    eleenn
    cA
    cN
    elee
    syl
    ibi
end
