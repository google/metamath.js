include "cnv.mm"
include "wcel.mm"
include "cims.mm"
include "cfv.mm"
include "cme.mm"
include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "cif.mm"
include "cba.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "cns.mm"
include "cpv.mm"
include "cgn.mm"
include "cnmcv.mm"
include "cn0v.mm"
include "eqid.mm"
include "elimnvu.mm"
include "imsmetlem.mm"
include "dedth.mm"
include "syl5eqel.mm"

theorem imsmet
  let cD: class D
  let cU: class U
  let cX: class X
  assume imsmet.1: |- X = ( BaseSet ` U )
  assume imsmet.8: |- D = ( IndMet ` U )


  assert |- ( U e. NrmCVec -> D e. ( Met ` X ) )

  proof
    cU
    cnv
    wcel
    #
    cD
    cU
    cims
    cfv
    #
    cX
    cme
    cfv
    #
    imsmet.8
    @0
    @1
    @2
    wcel
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
    cims
    cfv
    #
    @4
    cba
    cfv
    #
    cme
    cfv
    #
    wcel
    cU
    @3
    cU
    @4
    wceq
    #
    @1
    @5
    @2
    @7
    cU
    @4
    cims
    fveq2
    @8
    cX
    @6
    cme
    @8
    cX
    cU
    cba
    cfv
    @6
    imsmet.1
    cU
    @4
    cba
    fveq2
    syl5eq
    fveq2d
    eleq12d
    @5
    @4
    cns
    cfv
    #
    @4
    @4
    cpv
    cfv
    #
    @10
    cgn
    cfv
    #
    @4
    cnmcv
    cfv
    #
    @6
    @4
    cn0v
    cfv
    #
    @6
    eqid
    @10
    eqid
    @11
    eqid
    @9
    eqid
    @13
    eqid
    @12
    eqid
    @5
    eqid
    cU
    elimnvu
    imsmetlem
    dedth
    syl5eqel
end
