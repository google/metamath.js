include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "caddc.mm"
include "co.mm"
include "elnn0.mm"
include "nnaddcl.mm"
include "wa.mm"
include "oveq2.mm"
include "nncn.mm"
include "addid1d.mm"
include "sylan9eqr.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "jaodan.mm"
include "sylan2b.mm"

theorem nnnn0addcl
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ N e. NN0 ) -> ( M + N ) e. NN )

  proof
    cN
    cn0
    wcel
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    cM
    cN
    caddc
    co
    #
    cn
    wcel
    #
    cN
    elnn0
    @0
    @1
    @4
    @2
    cM
    cN
    nnaddcl
    @0
    @2
    wa
    @3
    cM
    cn
    @2
    @0
    @3
    cM
    cc0
    caddc
    co
    cM
    cN
    cc0
    cM
    caddc
    oveq2
    @0
    cM
    cM
    nncn
    addid1d
    sylan9eqr
    @0
    @2
    simpl
    eqeltrd
    jaodan
    sylan2b
end
