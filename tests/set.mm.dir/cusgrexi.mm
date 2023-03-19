include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "cusgr.mm"
include "ccplgr.mm"
include "ccusgr.mm"
include "usgrexi.mm"
include "cv.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cvtx.mm"
include "wral.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "wceq.mm"
include "cusgrexilem1.mm"
include "opvtxfv.mm"
include "eqcomd.mm"
include "mpdan.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "wne.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "wrex.mm"
include "eldifi.mm"
include "adantl.mm"
include "wb.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "simplr.mm"
include "jca.mm"
include "eldifsni.mm"
include "crn.mm"
include "cusgrexilem2.mm"
include "ciedg.mm"
include "edgval.mm"
include "opiedgfv.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "rexeqdv.mm"
include "eqid.mm"
include "nbgrel.mm"
include "syl3anbrc.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "difeq1d.mm"
include "raleqdv.mm"
include "uvtxel.mm"
include "sylanbrc.mm"
include "opex.mm"
include "iscplgr.mm"
include "mp1i.mm"
include "iscusgr.mm"

theorem cusgrexi
  let vx: setvar x
  let cP: class P
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vn: setvar n
  let vv: setvar v
  assume usgrexi.p: |- P = { x e. ~P V | ( # ` x ) = 2 }

  disjoint V x
  disjoint P x
  disjoint W x
  disjoint P e
  disjoint P n
  disjoint P v
  disjoint e n
  disjoint e v
  disjoint e x
  disjoint n v
  disjoint n x
  disjoint v x
  disjoint V e
  disjoint V n
  disjoint V v
  disjoint W e
  disjoint W n
  disjoint W v
  assert |- ( V e. W -> <. V , ( _I |` P ) >. e. ComplUSGraph )

  proof
    cV
    cW
    wcel
    #
    cV
    cid
    cP
    cres
    #
    cop
    #
    cusgr
    wcel
    @2
    ccplgr
    wcel
    #
    @2
    ccusgr
    wcel
    vx
    cP
    cV
    cW
    usgrexi.p
    usgrexi
    @0
    @3
    vv
    cv
    #
    @2
    cuvtx
    cfv
    wcel
    #
    vv
    @2
    cvtx
    cfv
    #
    wral
    #
    @0
    @7
    @5
    vv
    cV
    wral
    @0
    @5
    vv
    cV
    @0
    @4
    cV
    wcel
    #
    wa
    #
    @4
    @6
    wcel
    #
    vn
    cv
    #
    @2
    @4
    cnbgr
    co
    wcel
    #
    vn
    @6
    @4
    csn
    #
    cdif
    #
    wral
    #
    @5
    @0
    @8
    @10
    @0
    cV
    @6
    @4
    @0
    @1
    cvv
    wcel
    #
    cV
    @6
    wceq
    vx
    cP
    cV
    cW
    usgrexi.p
    cusgrexilem1
    #
    @0
    @16
    wa
    @6
    cV
    @1
    cV
    cW
    cvv
    opvtxfv
    #
    eqcomd
    mpdan
    eleq2d
    biimpa
    @9
    @15
    @12
    vn
    cV
    @13
    cdif
    #
    wral
    @9
    @12
    vn
    @19
    @9
    @11
    @19
    wcel
    #
    wa
    #
    @11
    @6
    wcel
    #
    @10
    wa
    @11
    @4
    wne
    #
    @4
    @11
    cpr
    ve
    cv
    wss
    #
    ve
    @2
    cedg
    cfv
    #
    wrex
    #
    @12
    @21
    @22
    @10
    @21
    @22
    @11
    cV
    wcel
    #
    @20
    @27
    @9
    @11
    cV
    @13
    eldifi
    adantl
    @0
    @22
    @27
    wb
    @8
    @20
    @0
    @6
    cV
    @11
    @0
    @16
    @6
    cV
    wceq
    #
    @17
    @18
    mpdan
    #
    eleq2d
    ad2antrr
    mpbird
    @21
    @10
    @8
    @0
    @8
    @20
    simplr
    @0
    @10
    @8
    wb
    @8
    @20
    @0
    @6
    cV
    @4
    @29
    eleq2d
    ad2antrr
    mpbird
    jca
    @20
    @23
    @9
    @11
    cV
    @4
    eldifsni
    adantl
    @21
    @26
    @24
    ve
    @1
    crn
    #
    wrex
    #
    vx
    vv
    cP
    ve
    vn
    cV
    cW
    usgrexi.p
    cusgrexilem2
    @0
    @26
    @31
    wb
    @8
    @20
    @0
    @24
    ve
    @25
    @30
    @0
    @25
    @2
    ciedg
    cfv
    #
    crn
    @30
    @2
    edgval
    @0
    @32
    @1
    @0
    @16
    @32
    @1
    wceq
    @17
    @1
    cV
    cW
    cvv
    opiedgfv
    mpdan
    rneqd
    syl5eq
    rexeqdv
    ad2antrr
    mpbird
    ve
    @25
    @2
    @11
    @6
    @4
    @6
    eqid
    #
    @25
    eqid
    nbgrel
    syl3anbrc
    ralrimiva
    @9
    @12
    vn
    @14
    @19
    @9
    @6
    cV
    @13
    @0
    @28
    @8
    @29
    adantr
    difeq1d
    raleqdv
    mpbird
    vn
    @2
    @4
    @6
    @33
    uvtxel
    sylanbrc
    ralrimiva
    @0
    @5
    vv
    @6
    cV
    @29
    raleqdv
    mpbird
    @2
    cvv
    wcel
    @3
    @7
    wb
    @0
    cV
    @1
    opex
    vv
    @2
    @6
    cvv
    @33
    iscplgr
    mp1i
    mpbird
    @2
    iscusgr
    sylanbrc
end
