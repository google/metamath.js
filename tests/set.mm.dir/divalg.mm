include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wreu.mm"
include "wa.mm"
include "c1.mm"
include "cif.mm"
include "eqeq1.mm"
include "3anbi3d.mm"
include "rexbidv.mm"
include "reubidv.mm"
include "fveq2.mm"
include "breq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "3anbi23d.mm"
include "cmin.mm"
include "cdvds.mm"
include "cn0.mm"
include "crab.mm"
include "1z.mm"
include "elimel.mm"
include "simpl.mm"
include "eleq1.mm"
include "elimdhyp.mm"
include "simpr.mm"
include "neeq1.mm"
include "ax-1ne0.mm"
include "eqid.mm"
include "divalglem10.mm"
include "dedth2h.mm"
include "3impb.mm"

theorem divalg
  let cD: class D
  let cN: class N
  let vr: setvar r
  let vq: setvar q

  disjoint D q
  disjoint D r
  disjoint q r
  disjoint N q
  disjoint N r
  assert |- ( ( N e. ZZ /\ D e. ZZ /\ D =/= 0 ) -> E! r e. ZZ E. q e. ZZ ( 0 <_ r /\ r < ( abs ` D ) /\ N = ( ( q x. D ) + r ) ) )

  proof
    cN
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    cD
    cc0
    wne
    #
    cc0
    vr
    cv
    #
    cle
    wbr
    #
    @3
    cD
    cabs
    cfv
    #
    clt
    wbr
    #
    cN
    vq
    cv
    #
    cD
    cmul
    co
    #
    @3
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vq
    cz
    wrex
    #
    vr
    cz
    wreu
    #
    @0
    @1
    @2
    wa
    #
    @13
    @4
    @6
    @0
    cN
    c1
    cif
    #
    @9
    wceq
    #
    w3a
    #
    vq
    cz
    wrex
    #
    vr
    cz
    wreu
    @4
    @3
    @14
    cD
    c1
    cif
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    @15
    @7
    @19
    cmul
    co
    #
    @3
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vq
    cz
    wrex
    #
    vr
    cz
    wreu
    cN
    cD
    c1
    c1
    cN
    @15
    wceq
    #
    @12
    @18
    vr
    cz
    @27
    @11
    @17
    vq
    cz
    @27
    @10
    @16
    @4
    @6
    cN
    @15
    @9
    eqeq1
    3anbi3d
    rexbidv
    reubidv
    cD
    @19
    wceq
    #
    @18
    @26
    vr
    cz
    @28
    @17
    @25
    vq
    cz
    @28
    @6
    @21
    @16
    @24
    @4
    @28
    @5
    @20
    @3
    clt
    cD
    @19
    cabs
    fveq2
    breq2d
    @28
    @9
    @23
    @15
    @28
    @8
    @22
    @3
    caddc
    cD
    @19
    @7
    cmul
    oveq2
    oveq1d
    eqeq2d
    3anbi23d
    rexbidv
    reubidv
    @19
    @19
    @15
    @3
    cmin
    co
    cdvds
    wbr
    vr
    cn0
    crab
    #
    @15
    vr
    vq
    cN
    c1
    cz
    1z
    elimel
    @14
    @1
    @19
    cz
    wcel
    c1
    cz
    wcel
    cD
    c1
    @1
    @2
    simpl
    cD
    @19
    cz
    eleq1
    c1
    @19
    cz
    eleq1
    1z
    elimdhyp
    @14
    @2
    @19
    cc0
    wne
    c1
    cc0
    wne
    cD
    c1
    @1
    @2
    simpr
    cD
    @19
    cc0
    neeq1
    c1
    @19
    cc0
    neeq1
    ax-1ne0
    elimdhyp
    @29
    eqid
    divalglem10
    dedth2h
    3impb
end
