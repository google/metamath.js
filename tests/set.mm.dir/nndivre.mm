include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "nnre.mm"
include "nnne0.mm"
include "jca.mm"
include "redivcl.mm"
include "3expb.mm"
include "sylan2.mm"

theorem nndivre
  let cA: class A
  let cN: class N


  assert |- ( ( A e. RR /\ N e. NN ) -> ( A / N ) e. RR )

  proof
    cN
    cn
    wcel
    #
    cA
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    cA
    cN
    cdiv
    co
    cr
    wcel
    #
    @0
    @2
    @3
    cN
    nnre
    cN
    nnne0
    jca
    @1
    @2
    @3
    @4
    cA
    cN
    redivcl
    3expb
    sylan2
end
