include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cle.mm"
include "msqge0.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "sqval.mm"
include "syl.mm"
include "breqtrrd.mm"

theorem sqge0
  let cA: class A


  assert |- ( A e. RR -> 0 <_ ( A ^ 2 ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cA
    cmul
    co
    #
    cA
    c2
    cexp
    co
    #
    cle
    cA
    msqge0
    @0
    cA
    cc
    wcel
    @2
    @1
    wceq
    cA
    recn
    cA
    sqval
    syl
    breqtrrd
end
