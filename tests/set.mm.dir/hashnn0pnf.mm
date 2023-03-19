include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "wo.mm"
include "cvv.mm"
include "wf.mm"
include "hashf.mm"
include "a1i.mm"
include "elex.mm"
include "ffvelrnd.mm"
include "elun.mm"
include "elsni.mm"
include "orim2i.mm"
include "sylbi.mm"
include "syl.mm"

theorem hashnn0pnf
  let cM: class M
  let cV: class V


  assert |- ( M e. V -> ( ( # ` M ) e. NN0 \/ ( # ` M ) = +oo ) )

  proof
    cM
    cV
    wcel
    #
    cM
    chash
    cfv
    #
    cn0
    cpnf
    csn
    #
    cun
    #
    wcel
    #
    @1
    cn0
    wcel
    #
    @1
    cpnf
    wceq
    #
    wo
    #
    @0
    cvv
    @3
    cM
    chash
    cvv
    @3
    chash
    wf
    @0
    hashf
    a1i
    cM
    cV
    elex
    ffvelrnd
    @4
    @5
    @1
    @2
    wcel
    #
    wo
    @7
    @1
    cn0
    @2
    elun
    @8
    @6
    @5
    @1
    cpnf
    elsni
    orim2i
    sylbi
    syl
end
