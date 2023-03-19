include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cfzo.mm"
include "zmodfz.mm"
include "wceq.mm"
include "nnz.mm"
include "fzoval.mm"
include "syl.mm"
include "adantl.mm"
include "eleqtrrd.mm"

theorem zmodfzo
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. NN ) -> ( A mod B ) e. ( 0 ..^ B ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    cA
    cB
    cmo
    co
    cc0
    cB
    c1
    cmin
    co
    cfz
    co
    #
    cc0
    cB
    cfzo
    co
    #
    cA
    cB
    zmodfz
    @1
    @3
    @2
    wceq
    #
    @0
    @1
    cB
    cz
    wcel
    @4
    cB
    nnz
    cc0
    cB
    fzoval
    syl
    adantl
    eleqtrrd
end
