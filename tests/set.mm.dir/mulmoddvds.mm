include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "simp1.mm"
include "wi.mm"
include "nnz.mm"
include "dvdsmultr1.mm"
include "syl3an1.mm"
include "dvdsmod0.mm"
include "syl6an.mm"

theorem mulmoddvds
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( N e. NN /\ A e. ZZ /\ B e. ZZ ) -> ( N || A -> ( ( A x. B ) mod N ) = 0 ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    w3a
    @0
    cN
    cA
    cdvds
    wbr
    #
    cN
    cA
    cB
    cmul
    co
    #
    cdvds
    wbr
    #
    @4
    cN
    cmo
    co
    cc0
    wceq
    @0
    @1
    @2
    simp1
    @0
    cN
    cz
    wcel
    @1
    @2
    @3
    @5
    wi
    cN
    nnz
    cN
    cA
    cB
    dvdsmultr1
    syl3an1
    cN
    @4
    dvdsmod0
    syl6an
end
