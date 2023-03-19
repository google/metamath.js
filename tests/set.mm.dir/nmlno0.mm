include "cnv.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "cif.mm"
include "clno.mm"
include "co.mm"
include "cnmoo.mm"
include "c0o.mm"
include "oveq1.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "eqeq2d.mm"
include "bibi12d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "eqid.mm"
include "elimnvu.mm"
include "nmlno0i.mm"
include "dedth2h.mm"
include "3impia.mm"

theorem nmlno0
  let cT: class T
  let cU: class U
  let cL: class L
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let vx: setvar x
  let cR: class R
  let cS: class S
  let cX: class X
  let cY: class Y
  assume nmlno0.3: |- N = ( U normOpOLD W )
  assume nmlno0.0: |- Z = ( U 0op W )
  assume nmlno0.7: |- L = ( U LnOp W )


  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T e. L ) -> ( ( N ` T ) = 0 <-> T = Z ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cT
    cL
    wcel
    #
    cT
    cN
    cfv
    #
    cc0
    wceq
    #
    cT
    cZ
    wceq
    #
    wb
    #
    @0
    @1
    @2
    @6
    wi
    cT
    @0
    cU
    caddc
    cmul
    cop
    cabs
    cop
    #
    cif
    #
    cW
    clno
    co
    #
    wcel
    #
    cT
    @8
    cW
    cnmoo
    co
    #
    cfv
    #
    cc0
    wceq
    #
    cT
    @8
    cW
    c0o
    co
    #
    wceq
    #
    wb
    #
    wi
    cT
    @8
    @1
    cW
    @7
    cif
    #
    clno
    co
    #
    wcel
    #
    cT
    @8
    @17
    cnmoo
    co
    #
    cfv
    #
    cc0
    wceq
    #
    cT
    @8
    @17
    c0o
    co
    #
    wceq
    #
    wb
    #
    wi
    cU
    cW
    @7
    @7
    cU
    @8
    wceq
    #
    @2
    @10
    @6
    @16
    @26
    cL
    @9
    cT
    @26
    cL
    cU
    cW
    clno
    co
    @9
    nmlno0.7
    cU
    @8
    cW
    clno
    oveq1
    syl5eq
    eleq2d
    @26
    @4
    @13
    @5
    @15
    @26
    @3
    @12
    cc0
    @26
    cT
    cN
    @11
    @26
    cN
    cU
    cW
    cnmoo
    co
    @11
    nmlno0.3
    cU
    @8
    cW
    cnmoo
    oveq1
    syl5eq
    fveq1d
    eqeq1d
    @26
    cZ
    @14
    cT
    @26
    cZ
    cU
    cW
    c0o
    co
    @14
    nmlno0.0
    cU
    @8
    cW
    c0o
    oveq1
    syl5eq
    eqeq2d
    bibi12d
    imbi12d
    cW
    @17
    wceq
    #
    @10
    @19
    @16
    @25
    @27
    @9
    @18
    cT
    cW
    @17
    @8
    clno
    oveq2
    eleq2d
    @27
    @13
    @22
    @15
    @24
    @27
    @12
    @21
    cc0
    @27
    cT
    @11
    @20
    cW
    @17
    @8
    cnmoo
    oveq2
    fveq1d
    eqeq1d
    @27
    @14
    @23
    cT
    cW
    @17
    @8
    c0o
    oveq2
    eqeq2d
    bibi12d
    imbi12d
    cT
    @8
    @18
    @20
    @17
    @23
    @20
    eqid
    @23
    eqid
    @18
    eqid
    cU
    elimnvu
    cW
    elimnvu
    nmlno0i
    dedth2h
    3impia
end
