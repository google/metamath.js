include "cr.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cle.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "adantr.mm"
include "nncn.mm"
include "adantl.mm"
include "1cnd.mm"
include "w3a.mm"
include "subsub.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "wbr.mm"
include "cc0.mm"
include "nnm1ge0.mm"
include "wb.mm"
include "nnre.mm"
include "peano2rem.mm"
include "syl.mm"
include "subge02.mm"
include "bicomd.mm"
include "sylan2.mm"
include "mpbird.mm"
include "eqbrtrd.mm"

theorem crctcshwlkn0lem1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. NN ) -> ( ( A - B ) + 1 ) <_ A )

  proof
    cA
    cr
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cA
    cB
    cmin
    co
    c1
    caddc
    co
    #
    cA
    cB
    c1
    cmin
    co
    #
    cmin
    co
    #
    cA
    cle
    @2
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @3
    @5
    wceq
    @0
    @6
    @1
    cA
    recn
    adantr
    @1
    @7
    @0
    cB
    nncn
    adantl
    @2
    1cnd
    @6
    @7
    @8
    w3a
    @5
    @3
    cA
    cB
    c1
    subsub
    eqcomd
    syl3anc
    @2
    @5
    cA
    cle
    wbr
    #
    cc0
    @4
    cle
    wbr
    #
    @1
    @10
    @0
    cB
    nnm1ge0
    adantl
    @1
    @0
    @4
    cr
    wcel
    #
    @9
    @10
    wb
    @1
    cB
    cr
    wcel
    @11
    cB
    nnre
    cB
    peano2rem
    syl
    @0
    @11
    wa
    @10
    @9
    cA
    @4
    subge02
    bicomd
    sylan2
    mpbird
    eqbrtrd
end
