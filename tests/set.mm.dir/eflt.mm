include "wtru.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "ce.mm"
include "cfv.mm"
include "wb.mm"
include "tru.mm"
include "cv.mm"
include "fveq2.mm"
include "ssid.mm"
include "reefcl.mm"
include "adantl.mm"
include "wi.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "c1.mm"
include "crp.mm"
include "simp2.mm"
include "simp1.mm"
include "resubcld.mm"
include "cc0.mm"
include "posdif.mm"
include "biimp3a.mm"
include "elrpd.mm"
include "efgt1.mm"
include "syl.mm"
include "reefcld.mm"
include "efgt0.mm"
include "ltmulgt11.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "caddc.mm"
include "cc.mm"
include "wceq.mm"
include "recnd.mm"
include "efadd.mm"
include "syl2anc.mm"
include "pncan3d.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "3expia.mm"
include "ltord1.mm"
include "mpan.mm"

theorem eflt
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> ( exp ` A ) < ( exp ` B ) ) )

  proof
    wtru
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    cA
    cB
    clt
    wbr
    cA
    ce
    cfv
    #
    cB
    ce
    cfv
    #
    clt
    wbr
    wb
    tru
    wtru
    vx
    vy
    vx
    cv
    #
    ce
    cfv
    #
    vy
    cv
    #
    ce
    cfv
    #
    cA
    cB
    cr
    @0
    @1
    @2
    @4
    ce
    fveq2
    @2
    cA
    ce
    fveq2
    @2
    cB
    ce
    fveq2
    cr
    ssid
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    wtru
    @2
    reefcl
    adantl
    @6
    @4
    cr
    wcel
    #
    wa
    @2
    @4
    clt
    wbr
    #
    @3
    @5
    clt
    wbr
    #
    wi
    wtru
    @6
    @8
    @9
    @10
    @6
    @8
    @9
    w3a
    #
    @3
    @3
    @4
    @2
    cmin
    co
    #
    ce
    cfv
    #
    cmul
    co
    #
    @5
    clt
    @11
    c1
    @13
    clt
    wbr
    #
    @3
    @14
    clt
    wbr
    #
    @11
    @12
    crp
    wcel
    @15
    @11
    @12
    @11
    @4
    @2
    @6
    @8
    @9
    simp2
    #
    @6
    @8
    @9
    simp1
    #
    resubcld
    #
    @6
    @8
    @9
    cc0
    @12
    clt
    wbr
    @2
    @4
    posdif
    biimp3a
    elrpd
    @12
    efgt1
    syl
    @11
    @7
    @13
    cr
    wcel
    cc0
    @3
    clt
    wbr
    #
    @15
    @16
    wb
    @11
    @2
    @18
    reefcld
    @11
    @12
    @19
    reefcld
    @11
    @6
    @20
    @18
    @2
    efgt0
    syl
    @3
    @13
    ltmulgt11
    syl3anc
    mpbid
    @11
    @2
    @12
    caddc
    co
    #
    ce
    cfv
    #
    @14
    @5
    @11
    @2
    cc
    wcel
    @12
    cc
    wcel
    @22
    @14
    wceq
    @11
    @2
    @18
    recnd
    #
    @11
    @12
    @19
    recnd
    @2
    @12
    efadd
    syl2anc
    @11
    @21
    @4
    ce
    @11
    @2
    @4
    @23
    @11
    @4
    @17
    recnd
    pncan3d
    fveq2d
    eqtr3d
    breqtrd
    3expia
    adantl
    ltord1
    mpan
end
