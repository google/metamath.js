include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cv.mm"
include "ciedg.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "csn.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "cfn.mm"
include "eqeq1i.mm"
include "dmeq.mm"
include "dm0.mm"
include "syl6eq.mm"
include "0fin.mm"
include "syl6eqel.mm"
include "sylbi.mm"
include "simpl.mm"
include "eqid.mm"
include "vtxdgfival.mm"
include "syl2an2.mm"
include "adantl.mm"
include "rabeq.mm"
include "rab0.mm"
include "fveq2d.mm"
include "hash0.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "oveq12d.mm"
include "syl.mm"
include "00id.mm"
include "eqtrd.mm"

theorem vtxdg0e
  let cU: class U
  let cG: class G
  let cI: class I
  let cV: class V
  let vu: setvar u
  let vx: setvar x
  let cW: class W
  assume vtxdgf.v: |- V = ( Vtx ` G )
  assume vtxdg0e.i: |- I = ( iEdg ` G )


  assert |- ( ( U e. V /\ I = (/) ) -> ( ( VtxDeg ` G ) ` U ) = 0 )

  proof
    cU
    cV
    wcel
    #
    cI
    c0
    wceq
    #
    wa
    #
    cU
    cG
    cvtxdg
    cfv
    cfv
    #
    cU
    vx
    cv
    cG
    ciedg
    cfv
    #
    cfv
    #
    wcel
    #
    vx
    @4
    cdm
    #
    crab
    #
    chash
    cfv
    #
    @5
    cU
    csn
    wceq
    #
    vx
    @7
    crab
    #
    chash
    cfv
    #
    caddc
    co
    #
    cc0
    @1
    @7
    cfn
    wcel
    #
    @0
    @0
    @3
    @13
    wceq
    @1
    @4
    c0
    wceq
    #
    @14
    cI
    @4
    c0
    vtxdg0e.i
    eqeq1i
    #
    @15
    @7
    c0
    cfn
    @15
    @7
    c0
    cdm
    c0
    @4
    c0
    dmeq
    dm0
    syl6eq
    #
    0fin
    syl6eqel
    sylbi
    @0
    @1
    simpl
    vx
    @7
    cU
    cG
    @4
    cV
    vtxdgf.v
    @4
    eqid
    @7
    eqid
    vtxdgfival
    syl2an2
    @2
    @13
    cc0
    cc0
    caddc
    co
    #
    cc0
    @2
    @7
    c0
    wceq
    #
    @13
    @18
    wceq
    @1
    @19
    @0
    @1
    @15
    @19
    @16
    @17
    sylbi
    adantl
    @19
    @9
    cc0
    @12
    cc0
    caddc
    @19
    @9
    c0
    chash
    cfv
    #
    cc0
    @19
    @8
    c0
    chash
    @19
    @8
    @6
    vx
    c0
    crab
    c0
    @6
    vx
    @7
    c0
    rabeq
    @6
    vx
    rab0
    syl6eq
    fveq2d
    hash0
    syl6eq
    @19
    @12
    @10
    vx
    c0
    crab
    #
    chash
    cfv
    #
    cc0
    @19
    @11
    @21
    chash
    @10
    vx
    @7
    c0
    rabeq
    fveq2d
    @22
    @20
    cc0
    @21
    c0
    chash
    @10
    vx
    rab0
    fveq2i
    hash0
    eqtri
    syl6eq
    oveq12d
    syl
    00id
    syl6eq
    eqtrd
end
