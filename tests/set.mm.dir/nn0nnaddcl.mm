include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "cc.mm"
include "wceq.mm"
include "nncn.mm"
include "nn0cn.mm"
include "addcom.mm"
include "syl2an.mm"
include "nnnn0addcl.mm"
include "eqeltrrd.mm"
include "ancoms.mm"

theorem nn0nnaddcl
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN ) -> ( M + N ) e. NN )

  proof
    cN
    cn
    wcel
    #
    cM
    cn0
    wcel
    #
    cM
    cN
    caddc
    co
    #
    cn
    wcel
    @0
    @1
    wa
    cN
    cM
    caddc
    co
    #
    @2
    cn
    @0
    cN
    cc
    wcel
    cM
    cc
    wcel
    @3
    @2
    wceq
    @1
    cN
    nncn
    cM
    nn0cn
    cN
    cM
    addcom
    syl2an
    cN
    cM
    nnnn0addcl
    eqeltrrd
    ancoms
end
