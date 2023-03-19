include "c1.mm"
include "c2.mm"
include "cop.mm"
include "cpr.mm"
include "wcel.mm"
include "cfv.mm"
include "cneg.mm"
include "wceq.mm"
include "cpmtr.mm"
include "crn.mm"
include "csn.mm"
include "prex.mm"
include "snid.mm"
include "fveq2i.mm"
include "rneqi.mm"
include "pmtrprfvalrn.mm"
include "eqtri.mm"
include "eleqtrri.mm"
include "psgnpmtr.mm"
include "ax-mp.mm"

theorem psgnprfval2
  let cB: class B
  let cD: class D
  let cT: class T
  let cG: class G
  let cN: class N
  let vs: setvar s
  let vw: setvar w
  let cX: class X
  assume psgnprfval.0: |- D = { 1 , 2 }
  assume psgnprfval.g: |- G = ( SymGrp ` D )
  assume psgnprfval.b: |- B = ( Base ` G )
  assume psgnprfval.t: |- T = ran ( pmTrsp ` D )
  assume psgnprfval.n: |- N = ( pmSgn ` D )


  assert |- ( N ` { <. 1 , 2 >. , <. 2 , 1 >. } ) = -u 1

  proof
    c1
    c2
    cop
    #
    c2
    c1
    cop
    #
    cpr
    #
    cT
    wcel
    @2
    cN
    cfv
    c1
    cneg
    wceq
    @2
    cD
    cpmtr
    cfv
    #
    crn
    #
    cT
    @2
    @2
    csn
    #
    @4
    @2
    @0
    @1
    prex
    snid
    @4
    c1
    c2
    cpr
    #
    cpmtr
    cfv
    #
    crn
    @5
    @3
    @7
    cD
    @6
    cpmtr
    psgnprfval.0
    fveq2i
    rneqi
    pmtrprfvalrn
    eqtri
    eleqtrri
    psgnprfval.t
    eleqtrri
    cD
    @2
    cT
    cG
    cN
    psgnprfval.g
    psgnprfval.t
    psgnprfval.n
    psgnpmtr
    ax-mp
end
