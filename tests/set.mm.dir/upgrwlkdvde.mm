include "cupgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "upgriswlk.mm"
include "wa.mm"
include "wf1.mm"
include "df-f1.mm"
include "simplbi2.mm"
include "3ad2ant2.mm"
include "impcom.mm"
include "simpr1.mm"
include "jca.mm"
include "simpr3.mm"
include "upgrwlkdvdelem.mm"
include "sylc.mm"
include "expcom.mm"
include "syl6bi.mm"
include "3imp.mm"

theorem upgrwlkdvde
  let cP: class P
  let cF: class F
  let cG: class G
  let vk: setvar k


  assert |- ( ( G e. UPGraph /\ F ( Walks ` G ) P /\ Fun `' P ) -> Fun `' F )

  proof
    cG
    cupgr
    wcel
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cP
    ccnv
    wfun
    #
    cF
    ccnv
    wfun
    #
    @0
    @1
    cF
    cG
    ciedg
    cfv
    #
    cdm
    cword
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    vk
    cv
    #
    cF
    cfv
    @4
    cfv
    @10
    cP
    cfv
    @10
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    vk
    cc0
    @6
    cfzo
    co
    wral
    #
    w3a
    #
    @2
    @3
    wi
    cP
    vk
    cF
    cG
    @4
    @8
    @8
    eqid
    @4
    eqid
    upgriswlk
    @2
    @12
    @3
    @2
    @12
    wa
    #
    @7
    @8
    cP
    wf1
    #
    @5
    wa
    @11
    @3
    @13
    @14
    @5
    @12
    @2
    @14
    @9
    @5
    @2
    @14
    wi
    @11
    @14
    @9
    @2
    @7
    @8
    cP
    df-f1
    simplbi2
    3ad2ant2
    impcom
    @2
    @5
    @9
    @11
    simpr1
    jca
    @2
    @5
    @9
    @11
    simpr3
    cP
    vk
    cF
    @4
    @8
    upgrwlkdvdelem
    sylc
    expcom
    syl6bi
    3imp
end
