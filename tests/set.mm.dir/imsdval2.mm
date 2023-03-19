include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cnsb.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "eqid.mm"
include "imsdval.mm"
include "nvmval.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem imsdval2
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  assume imsdval2.1: |- X = ( BaseSet ` U )
  assume imsdval2.2: |- G = ( +v ` U )
  assume imsdval2.4: |- S = ( .sOLD ` U )
  assume imsdval2.6: |- N = ( normCV ` U )
  assume imsdval2.8: |- D = ( IndMet ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A D B ) = ( N ` ( A G ( -u 1 S B ) ) ) )

  proof
    cU
    cnv
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    w3a
    #
    cA
    cB
    cD
    co
    cA
    cB
    cU
    cnsb
    cfv
    #
    co
    #
    cN
    cfv
    cA
    c1
    cneg
    cB
    cS
    co
    cG
    co
    #
    cN
    cfv
    cA
    cB
    cD
    cU
    @1
    cN
    cX
    imsdval2.1
    @1
    eqid
    #
    imsdval2.6
    imsdval2.8
    imsdval
    @0
    @2
    @3
    cN
    cA
    cB
    cS
    cU
    cG
    @1
    cX
    imsdval2.1
    imsdval2.2
    imsdval2.4
    @4
    nvmval
    fveq2d
    eqtrd
end
