include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "cfv.mm"
include "co.mm"
include "ccom.mm"
include "wceq.mm"
include "imsval.mm"
include "3ad2ant1.mm"
include "fveq1d.mm"
include "cxp.mm"
include "wf.mm"
include "wa.mm"
include "nvmf.mm"
include "opelxpi.mm"
include "fvco3.mm"
include "syl2an.mm"
include "3impb.mm"
include "eqtrd.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"

theorem imsdval
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let cM: class M
  let cN: class N
  let cX: class X
  assume imsdval.1: |- X = ( BaseSet ` U )
  assume imsdval.3: |- M = ( -v ` U )
  assume imsdval.6: |- N = ( normCV ` U )
  assume imsdval.8: |- D = ( IndMet ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A D B ) = ( N ` ( A M B ) ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cop
    #
    cD
    cfv
    #
    @4
    cM
    cfv
    #
    cN
    cfv
    #
    cA
    cB
    cD
    co
    cA
    cB
    cM
    co
    #
    cN
    cfv
    @3
    @5
    @4
    cN
    cM
    ccom
    #
    cfv
    #
    @7
    @3
    @4
    cD
    @9
    @0
    @1
    cD
    @9
    wceq
    @2
    cD
    cU
    cM
    cN
    imsdval.3
    imsdval.6
    imsdval.8
    imsval
    3ad2ant1
    fveq1d
    @0
    @1
    @2
    @10
    @7
    wceq
    #
    @0
    cX
    cX
    cxp
    #
    cX
    cM
    wf
    @4
    @12
    wcel
    @11
    @1
    @2
    wa
    cU
    cM
    cX
    imsdval.1
    imsdval.3
    nvmf
    cA
    cB
    cX
    cX
    opelxpi
    @12
    cX
    @4
    cN
    cM
    fvco3
    syl2an
    3impb
    eqtrd
    cA
    cB
    cD
    df-ov
    @8
    @6
    cN
    cA
    cB
    cM
    df-ov
    fveq2i
    3eqtr4g
end
