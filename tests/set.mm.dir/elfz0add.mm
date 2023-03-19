include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "cz.mm"
include "nn0z.mm"
include "uzid.mm"
include "syl.mm"
include "id.mm"
include "anim12i.mm"
include "uzaddcl.mm"
include "fzss2.mm"
include "sseld.mm"

theorem elfz0add
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( A e. NN0 /\ B e. NN0 ) -> ( N e. ( 0 ... A ) -> N e. ( 0 ... ( A + B ) ) ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    #
    cc0
    cA
    cfz
    co
    #
    cc0
    cA
    cB
    caddc
    co
    #
    cfz
    co
    #
    cN
    @2
    @4
    cA
    cuz
    cfv
    #
    wcel
    #
    @3
    @5
    wss
    @2
    cA
    @6
    wcel
    #
    @1
    wa
    @7
    @0
    @8
    @1
    @1
    @0
    cA
    cz
    wcel
    @8
    cA
    nn0z
    cA
    uzid
    syl
    @1
    id
    anim12i
    cB
    cA
    cA
    uzaddcl
    syl
    cA
    cc0
    @4
    fzss2
    syl
    sseld
end
