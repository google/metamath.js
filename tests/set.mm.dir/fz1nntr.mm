include "cn.mm"
include "wceq.mm"
include "wcel.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "wss.mm"
include "fzossnn.mm"
include "sseq2.mm"
include "mpbiri.mm"
include "adantr.mm"
include "wi.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzouz2.mm"
include "fzoss2.mm"
include "syl.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "imp.mm"
include "jaoian.mm"

theorem fz1nntr
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( ( A = NN \/ A = ( 1 ..^ M ) ) /\ N e. A ) -> ( 1 ..^ N ) C_ A )

  proof
    cA
    cn
    wceq
    #
    cN
    cA
    wcel
    #
    c1
    cN
    cfzo
    co
    #
    cA
    wss
    #
    cA
    c1
    cM
    cfzo
    co
    #
    wceq
    #
    @0
    @3
    @1
    @0
    @3
    @2
    cn
    wss
    cN
    fzossnn
    cA
    cn
    @2
    sseq2
    mpbiri
    adantr
    @5
    @1
    @3
    @5
    @1
    @3
    wi
    cN
    @4
    wcel
    #
    @2
    @4
    wss
    #
    wi
    @6
    cM
    cN
    cuz
    cfv
    wcel
    @7
    cN
    c1
    cM
    elfzouz2
    cN
    c1
    cM
    fzoss2
    syl
    @5
    @1
    @6
    @3
    @7
    cA
    @4
    cN
    eleq2
    cA
    @4
    @2
    sseq2
    imbi12d
    mpbiri
    imp
    jaoian
end
