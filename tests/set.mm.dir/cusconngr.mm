include "cuhgr.mm"
include "wcel.mm"
include "ccplgr.mm"
include "wa.mm"
include "cconngr.mm"
include "cv.mm"
include "cpthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "cvtx.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "eqid.mm"
include "iscplgredg.mm"
include "simp-4l.mm"
include "simpr.mm"
include "eldifi.mm"
include "anim12i.mm"
include "adantr.mm"
include "wi.mm"
include "id.mm"
include "weq.mm"
include "wb.mm"
include "sseq2.mm"
include "adantl.mm"
include "rspcedv.mm"
include "imp.mm"
include "1pthon2v.mm"
include "syl3anc.mm"
include "ex.mm"
include "rexlimdva.mm"
include "ralimdva.mm"
include "sylbid.mm"
include "isconngr1.mm"
include "mpbird.mm"

theorem cusconngr
  let cG: class G
  let vc: setvar c
  let ve: setvar e
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p


  assert |- ( ( G e. UHGraph /\ G e. ComplGraph ) -> G e. ConnGraph )

  proof
    cG
    cuhgr
    wcel
    #
    cG
    ccplgr
    wcel
    #
    wa
    cG
    cconngr
    wcel
    #
    vf
    cv
    vp
    cv
    vk
    cv
    #
    vn
    cv
    #
    cG
    cpthson
    cfv
    co
    wbr
    vp
    wex
    vf
    wex
    #
    vn
    cG
    cvtx
    cfv
    #
    @3
    csn
    #
    cdif
    #
    wral
    #
    vk
    @6
    wral
    #
    @0
    @1
    @10
    @0
    @1
    @3
    @4
    cpr
    #
    ve
    cv
    #
    wss
    #
    ve
    cG
    cedg
    cfv
    #
    wrex
    #
    vn
    @8
    wral
    #
    vk
    @6
    wral
    @10
    vk
    ve
    vn
    @14
    cG
    @6
    cuhgr
    @6
    eqid
    #
    @14
    eqid
    #
    iscplgredg
    @0
    @16
    @9
    vk
    @6
    @0
    @3
    @6
    wcel
    #
    wa
    #
    @15
    @5
    vn
    @8
    @20
    @4
    @8
    wcel
    #
    wa
    #
    @13
    @5
    ve
    @14
    @22
    @12
    @14
    wcel
    #
    wa
    #
    @13
    @5
    @24
    @13
    wa
    @0
    @19
    @4
    @6
    wcel
    #
    wa
    #
    @11
    vc
    cv
    #
    wss
    #
    vc
    @14
    wrex
    #
    @5
    @0
    @19
    @21
    @23
    @13
    simp-4l
    @24
    @26
    @13
    @22
    @26
    @23
    @20
    @19
    @21
    @25
    @0
    @19
    simpr
    @4
    @6
    @7
    eldifi
    anim12i
    adantr
    adantr
    @24
    @13
    @29
    @23
    @13
    @29
    wi
    @22
    @23
    @28
    @13
    vc
    @12
    @14
    @23
    id
    vc
    ve
    weq
    @28
    @13
    wb
    @23
    @27
    @12
    @11
    sseq2
    adantl
    rspcedv
    adantl
    imp
    @3
    @4
    vc
    vf
    @14
    cG
    @6
    vp
    @17
    @18
    1pthon2v
    syl3anc
    ex
    rexlimdva
    ralimdva
    ralimdva
    sylbid
    imp
    @0
    @2
    @10
    wb
    @1
    vf
    vk
    vn
    cG
    @6
    cuhgr
    vp
    @17
    isconngr1
    adantr
    mpbird
end
