include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cmo.mm"
include "wceq.mm"
include "cc.mm"
include "nn0cn.mm"
include "nncn.mm"
include "addcom.mm"
include "syl2an.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "addmodid.mm"
include "eqtrd.mm"

theorem addmodidr
  let cA: class A
  let cM: class M


  assert |- ( ( A e. NN0 /\ M e. NN /\ A < M ) -> ( ( A + M ) mod M ) = A )

  proof
    cA
    cn0
    wcel
    #
    cM
    cn
    wcel
    #
    cA
    cM
    clt
    wbr
    #
    w3a
    #
    cA
    cM
    caddc
    co
    #
    cM
    cmo
    co
    cM
    cA
    caddc
    co
    #
    cM
    cmo
    co
    cA
    @3
    @4
    @5
    cM
    cmo
    @0
    @1
    @4
    @5
    wceq
    #
    @2
    @0
    cA
    cc
    wcel
    cM
    cc
    wcel
    @6
    @1
    cA
    nn0cn
    cM
    nncn
    cA
    cM
    addcom
    syl2an
    3adant3
    oveq1d
    cA
    cM
    addmodid
    eqtrd
end
