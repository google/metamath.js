include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "id.mm"
include "eqidd.mm"
include "csubg.mm"
include "cbs.mm"
include "cmre.mm"
include "wcel.mm"
include "wss.mm"
include "cgrp.mm"
include "cacs.mm"
include "dprdgrp.mm"
include "eqid.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "cv.mm"
include "ciun.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "dprdf.mm"
include "ffn.mm"
include "syl.mm"
include "fniunfv.mm"
include "wral.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "dprdub.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstr3d.mm"
include "dprdssv.mm"
include "syl6ss.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "eqimss.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "mrcssidd.mm"
include "adantr.mm"
include "sstrd.mm"
include "dprdlub.mm"
include "dprdsubg.mm"
include "mrcsscl.mm"
include "syl3anc.mm"
include "eqssd.mm"

theorem dprdspan
  let cS: class S
  let cG: class G
  let cK: class K
  let vk: setvar k
  assume dprdspan.k: |- K = ( mrCls ` ( SubGrp ` G ) )


  assert |- ( G dom DProd S -> ( G DProd S ) = ( K ` U. ran S ) )

  proof
    cG
    cS
    cdprd
    cdm
    wbr
    #
    cG
    cS
    cdprd
    co
    #
    cS
    crn
    cuni
    #
    cK
    cfv
    #
    @0
    cS
    @3
    vk
    cG
    cS
    cdm
    #
    @0
    id
    @0
    @4
    eqidd
    @0
    cG
    csubg
    cfv
    #
    cG
    cbs
    cfv
    #
    cmre
    cfv
    wcel
    #
    @2
    @6
    wss
    @3
    @5
    wcel
    @0
    cG
    cgrp
    wcel
    @5
    @6
    cacs
    cfv
    wcel
    @7
    cS
    cG
    dprdgrp
    @6
    cG
    @6
    eqid
    #
    subgacs
    @5
    @6
    acsmre
    3syl
    #
    @0
    @2
    @1
    @6
    @0
    @2
    vk
    @4
    vk
    cv
    #
    cS
    cfv
    #
    ciun
    #
    @1
    @0
    cS
    @4
    wfn
    #
    @12
    @2
    wceq
    #
    @0
    @4
    @5
    cS
    wf
    @13
    cS
    cG
    dprdf
    @4
    @5
    cS
    ffn
    syl
    vk
    @4
    cS
    fniunfv
    syl
    #
    @0
    @11
    @1
    wss
    #
    vk
    @4
    wral
    @12
    @1
    wss
    @0
    @16
    vk
    @4
    @0
    @10
    @4
    wcel
    #
    wa
    #
    cS
    cG
    @4
    @10
    @0
    @17
    simpl
    @18
    @4
    eqidd
    @0
    @17
    simpr
    dprdub
    ralrimiva
    vk
    @4
    @11
    @1
    iunss
    sylibr
    eqsstr3d
    #
    @6
    cS
    cG
    @8
    dprdssv
    syl6ss
    #
    @5
    @2
    cK
    @6
    dprdspan.k
    mrccl
    syl2anc
    @18
    @11
    @2
    @3
    @0
    @11
    @2
    wss
    #
    vk
    @4
    @0
    @12
    @2
    wss
    #
    @21
    vk
    @4
    wral
    @0
    @14
    @22
    @15
    @12
    @2
    eqimss
    syl
    vk
    @4
    @11
    @2
    iunss
    sylib
    r19.21bi
    @0
    @2
    @3
    wss
    @17
    @0
    @5
    @2
    cK
    @6
    @9
    dprdspan.k
    @20
    mrcssidd
    adantr
    sstrd
    dprdlub
    @0
    @7
    @2
    @1
    wss
    @1
    @5
    wcel
    @3
    @1
    wss
    @9
    @19
    cS
    cG
    dprdsubg
    @5
    @2
    cK
    @1
    @6
    dprdspan.k
    mrcsscl
    syl3anc
    eqssd
end
