include "cc.mm"
include "caddc.mm"
include "cv.mm"
include "cplr.mm"
include "co.mm"
include "cep.mm"
include "ccnv.mm"
include "cnr.mm"
include "dfcnqs.mm"
include "addcnsrec.mm"
include "wcel.mm"
include "wa.mm"
include "addclsr.mm"
include "anim12i.mm"
include "an4s.mm"
include "addasssr.mm"
include "ecovass.mm"

theorem axaddass
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) + C ) = ( A + ( B + C ) ) )

  proof
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cC
    cc
    caddc
    vw
    cv
    #
    vu
    cv
    #
    cplr
    co
    #
    cep
    ccnv
    cnr
    vx
    cv
    #
    vz
    cv
    #
    cplr
    co
    #
    vy
    cv
    #
    @0
    cplr
    co
    #
    @5
    vv
    cv
    #
    cplr
    co
    @7
    @1
    cplr
    co
    @3
    @4
    @8
    cplr
    co
    #
    cplr
    co
    @6
    @2
    cplr
    co
    @9
    dfcnqs
    @3
    @6
    @4
    @0
    addcnsrec
    @4
    @0
    @8
    @1
    addcnsrec
    @5
    @7
    @8
    @1
    addcnsrec
    @3
    @6
    @9
    @2
    addcnsrec
    @3
    cnr
    wcel
    #
    @4
    cnr
    wcel
    #
    @6
    cnr
    wcel
    #
    @0
    cnr
    wcel
    #
    @5
    cnr
    wcel
    #
    @7
    cnr
    wcel
    #
    wa
    @10
    @11
    wa
    @14
    @12
    @13
    wa
    @15
    @3
    @4
    addclsr
    @6
    @0
    addclsr
    anim12i
    an4s
    @11
    @8
    cnr
    wcel
    #
    @13
    @1
    cnr
    wcel
    #
    @9
    cnr
    wcel
    #
    @2
    cnr
    wcel
    #
    wa
    @11
    @16
    wa
    @18
    @13
    @17
    wa
    @19
    @4
    @8
    addclsr
    @0
    @1
    addclsr
    anim12i
    an4s
    @3
    @4
    @8
    addasssr
    @6
    @0
    @1
    addasssr
    ecovass
end
