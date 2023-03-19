include "cxme.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cds.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "cstrkgc.mm"
include "elex.mm"
include "eqid.mm"
include "xmssym.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "w3a.mm"
include "cc0.mm"
include "simpl.mm"
include "simpr3.mm"
include "equid.mm"
include "xmseq0.mm"
include "mpbiri.mm"
include "syl3anc.mm"
include "eqeq2d.mm"
include "wb.mm"
include "3adant3r3.mm"
include "bitrd.mm"
include "biimpd.mm"
include "ralrimivvva.mm"
include "jca.mm"
include "citv.mm"
include "istrkgc.mm"
include "sylanbrc.mm"

theorem xmstrkgc
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( G e. *MetSp -> G e. TarskiGC )

  proof
    cG
    cxme
    wcel
    #
    cG
    cvv
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cG
    cds
    cfv
    #
    co
    #
    @2
    @1
    @3
    co
    wceq
    #
    vy
    cG
    cbs
    cfv
    #
    wral
    vx
    @6
    wral
    #
    @4
    vz
    cv
    #
    @8
    @3
    co
    #
    wceq
    #
    @1
    @2
    wceq
    #
    wi
    #
    vz
    @6
    wral
    vy
    @6
    wral
    vx
    @6
    wral
    #
    wa
    cG
    cstrkgc
    wcel
    cG
    cxme
    elex
    @0
    @7
    @13
    @0
    @5
    vx
    vy
    @6
    @6
    @0
    @1
    @6
    wcel
    #
    @2
    @6
    wcel
    #
    @5
    @1
    @2
    @3
    cG
    @6
    @6
    eqid
    #
    @3
    eqid
    #
    xmssym
    3expb
    ralrimivva
    @0
    @12
    vx
    vy
    vz
    @6
    @6
    @6
    @0
    @14
    @15
    @8
    @6
    wcel
    #
    w3a
    #
    wa
    #
    @10
    @11
    @20
    @10
    @4
    cc0
    wceq
    #
    @11
    @20
    @9
    cc0
    @4
    @20
    @0
    @18
    @18
    @9
    cc0
    wceq
    #
    @0
    @19
    simpl
    @0
    @14
    @15
    @18
    simpr3
    #
    @23
    @0
    @18
    @18
    w3a
    @22
    @8
    @8
    wceq
    vz
    equid
    @8
    @8
    @3
    cG
    @6
    @16
    @17
    xmseq0
    mpbiri
    syl3anc
    eqeq2d
    @0
    @14
    @15
    @21
    @11
    wb
    @18
    @1
    @2
    @3
    cG
    @6
    @16
    @17
    xmseq0
    3adant3r3
    bitrd
    biimpd
    ralrimivvva
    jca
    vx
    vy
    vz
    @6
    cG
    cG
    citv
    cfv
    #
    @3
    @16
    @17
    @24
    eqid
    istrkgc
    sylanbrc
end
