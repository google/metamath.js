include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "cima.mm"
include "crn.mm"
include "clss.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "eqid.mm"
include "lmhmf.mm"
include "ffn.mm"
include "fnima.mm"
include "3syl.mm"
include "clmod.mm"
include "lmhmlmod1.mm"
include "lss1.mm"
include "syl.mm"
include "lmhmima.mm"
include "mpdan.mm"
include "eqeltrrd.mm"

theorem lmhmrnlss
  let cS: class S
  let cT: class T
  let cF: class F


  assert |- ( F e. ( S LMHom T ) -> ran F e. ( LSubSp ` T ) )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cF
    cS
    cbs
    cfv
    #
    cima
    #
    cF
    crn
    #
    cT
    clss
    cfv
    #
    @0
    @1
    cT
    cbs
    cfv
    #
    cF
    wf
    cF
    @1
    wfn
    @2
    @3
    wceq
    @1
    @5
    cS
    cT
    cF
    @1
    eqid
    #
    @5
    eqid
    lmhmf
    @1
    @5
    cF
    ffn
    @1
    cF
    fnima
    3syl
    @0
    @1
    cS
    clss
    cfv
    #
    wcel
    #
    @2
    @4
    wcel
    @0
    cS
    clmod
    wcel
    @8
    cS
    cT
    cF
    lmhmlmod1
    @7
    @1
    cS
    @6
    @7
    eqid
    #
    lss1
    syl
    cS
    cT
    @1
    cF
    @7
    @4
    @9
    @4
    eqid
    lmhmima
    mpdan
    eqeltrrd
end
