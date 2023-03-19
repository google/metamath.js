include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "wceq.mm"
include "wn.mm"
include "cgcd.mm"
include "co.mm"
include "cn.mm"
include "neneq.mm"
include "intnand.mm"
include "anim2i.mm"
include "3impa.mm"
include "gcdn0cl.mm"
include "syl.mm"

theorem gcd2n0cl
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ N =/= 0 ) -> ( M gcd N ) e. NN )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    w3a
    @0
    @1
    wa
    #
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wa
    wn
    #
    wa
    #
    cM
    cN
    cgcd
    co
    cn
    wcel
    @0
    @1
    @2
    @7
    @2
    @6
    @3
    @2
    @5
    @4
    cN
    cc0
    neneq
    intnand
    anim2i
    3impa
    cM
    cN
    gcdn0cl
    syl
end
