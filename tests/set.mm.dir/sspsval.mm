include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "co.mm"
include "cxp.mm"
include "cres.mm"
include "ssps.mm"
include "oveqd.mm"
include "ovres.mm"
include "sylan9eq.mm"

theorem sspsval
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume ssps.y: |- Y = ( BaseSet ` W )
  assume ssps.s: |- S = ( .sOLD ` U )
  assume ssps.r: |- R = ( .sOLD ` W )
  assume ssps.h: |- H = ( SubSp ` U )


  assert |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. CC /\ B e. Y ) ) -> ( A R B ) = ( A S B ) )

  proof
    cU
    cnv
    wcel
    cW
    cH
    wcel
    wa
    #
    cA
    cc
    wcel
    cB
    cY
    wcel
    wa
    cA
    cB
    cR
    co
    cA
    cB
    cS
    cc
    cY
    cxp
    cres
    #
    co
    cA
    cB
    cS
    co
    @0
    cR
    @1
    cA
    cB
    cR
    cS
    cU
    cH
    cW
    cY
    ssps.y
    ssps.s
    ssps.r
    ssps.h
    ssps
    oveqd
    cA
    cB
    cc
    cY
    cS
    ovres
    sylan9eq
end
