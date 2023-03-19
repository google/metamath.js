include "wcel.mm"
include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wa.mm"
include "ccn.mm"
include "blocnilem.mm"
include "blocni.mm"
include "sylibr.mm"

theorem lnocni
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cT: class T
  let cU: class U
  let cJ: class J
  let cK: class K
  let cL: class L
  let cW: class W
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume blocni.8: |- C = ( IndMet ` U )
  assume blocni.d: |- D = ( IndMet ` W )
  assume blocni.j: |- J = ( MetOpen ` C )
  assume blocni.k: |- K = ( MetOpen ` D )
  assume blocni.4: |- L = ( U LnOp W )
  assume blocni.5: |- B = ( U BLnOp W )
  assume blocni.u: |- U e. NrmCVec
  assume blocni.w: |- W e. NrmCVec
  assume blocni.l: |- T e. L
  assume lnocni.1: |- X = ( BaseSet ` U )


  assert |- ( ( P e. X /\ T e. ( ( J CnP K ) ` P ) ) -> T e. ( J Cn K ) )

  proof
    cP
    cX
    wcel
    cT
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    wa
    cT
    cB
    wcel
    cT
    cJ
    cK
    ccn
    co
    wcel
    cB
    cC
    cD
    cP
    cT
    cU
    cJ
    cK
    cL
    cW
    cX
    blocni.8
    blocni.d
    blocni.j
    blocni.k
    blocni.4
    blocni.5
    blocni.u
    blocni.w
    blocni.l
    lnocni.1
    blocnilem
    cB
    cC
    cD
    cT
    cU
    cJ
    cK
    cL
    cW
    blocni.8
    blocni.d
    blocni.j
    blocni.k
    blocni.4
    blocni.5
    blocni.u
    blocni.w
    blocni.l
    blocni
    sylibr
end
