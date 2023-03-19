include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cxp.mm"
include "cres.mm"
include "sspg.mm"
include "oveqd.mm"
include "ovres.mm"
include "sylan9eq.mm"

theorem sspgval
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume sspg.y: |- Y = ( BaseSet ` W )
  assume sspg.g: |- G = ( +v ` U )
  assume sspg.f: |- F = ( +v ` W )
  assume sspg.h: |- H = ( SubSp ` U )


  assert |- ( ( ( U e. NrmCVec /\ W e. H ) /\ ( A e. Y /\ B e. Y ) ) -> ( A F B ) = ( A G B ) )

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
    cY
    wcel
    cB
    cY
    wcel
    wa
    cA
    cB
    cF
    co
    cA
    cB
    cG
    cY
    cY
    cxp
    cres
    #
    co
    cA
    cB
    cG
    co
    @0
    cF
    @1
    cA
    cB
    cU
    cF
    cG
    cH
    cW
    cY
    sspg.y
    sspg.g
    sspg.f
    sspg.h
    sspg
    oveqd
    cA
    cB
    cY
    cY
    cG
    ovres
    sylan9eq
end
