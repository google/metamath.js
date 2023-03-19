include "wcel.mm"
include "ctp.mm"
include "c0.mm"
include "wne.mm"
include "tpid3g.mm"
include "tprot.mm"
include "syl6eleqr.mm"
include "ne0i.mm"
include "3syl.mm"

theorem tpnzd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume tpnzd.1: |- ( ph -> A e. V )


  assert |- ( ph -> { A , B , C } =/= (/) )

  proof
    wph
    cA
    cV
    wcel
    #
    cA
    cA
    cB
    cC
    ctp
    #
    wcel
    @1
    c0
    wne
    tpnzd.1
    @0
    cA
    cB
    cC
    cA
    ctp
    @1
    cA
    cV
    cB
    cC
    tpid3g
    cA
    cB
    cC
    tprot
    syl6eleqr
    @1
    cA
    ne0i
    3syl
end
