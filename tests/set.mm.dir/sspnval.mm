include "cnv.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cres.mm"
include "sspn.mm"
include "fveq1d.mm"
include "fvres.mm"
include "sylan9eq.mm"
include "3impa.mm"

theorem sspnval
  let cA: class A
  let cU: class U
  let cH: class H
  let cM: class M
  let cN: class N
  let cW: class W
  let cY: class Y
  let vx: setvar x
  assume sspn.y: |- Y = ( BaseSet ` W )
  assume sspn.n: |- N = ( normCV ` U )
  assume sspn.m: |- M = ( normCV ` W )
  assume sspn.h: |- H = ( SubSp ` U )


  assert |- ( ( U e. NrmCVec /\ W e. H /\ A e. Y ) -> ( M ` A ) = ( N ` A ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cH
    wcel
    #
    cA
    cY
    wcel
    #
    cA
    cM
    cfv
    #
    cA
    cN
    cfv
    #
    wceq
    @0
    @1
    wa
    #
    @2
    @3
    cA
    cN
    cY
    cres
    #
    cfv
    @4
    @5
    cA
    cM
    @6
    cU
    cH
    cM
    cN
    cW
    cY
    sspn.y
    sspn.n
    sspn.m
    sspn.h
    sspn
    fveq1d
    cA
    cY
    cN
    fvres
    sylan9eq
    3impa
end
