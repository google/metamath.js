include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "codz.mm"
include "cfv.mm"
include "cexp.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "odzcllem.mm"
include "simpld.mm"

theorem odzcl
  let cA: class A
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cK: class K


  assert |- ( ( N e. NN /\ A e. ZZ /\ ( A gcd N ) = 1 ) -> ( ( odZ ` N ) ` A ) e. NN )

  proof
    cN
    cn
    wcel
    cA
    cz
    wcel
    cA
    cN
    cgcd
    co
    c1
    wceq
    w3a
    cA
    cN
    codz
    cfv
    cfv
    #
    cn
    wcel
    cN
    cA
    @0
    cexp
    co
    c1
    cmin
    co
    cdvds
    wbr
    cA
    cN
    odzcllem
    simpld
end
