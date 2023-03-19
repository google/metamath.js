include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "coppg.mm"
include "clsm.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "simpl3.mm"
include "eqid.mm"
include "oppgsubg.mm"
include "syl6eleq.mm"
include "simpl2.mm"
include "simpl1.mm"
include "simpr.mm"
include "lsmmod.mm"
include "syl31anc.mm"
include "eqcomd.mm"
include "incom.mm"
include "oveq2i.mm"
include "3eqtr3g.mm"
include "oppglsm.mm"
include "ineq2i.mm"

theorem lsmmod2
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lsmmod.p: |- .(+) = ( LSSum ` G )


  assert |- ( ( ( S e. ( SubGrp ` G ) /\ T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) ) /\ U C_ S ) -> ( S i^i ( T .(+) U ) ) = ( ( S i^i T ) .(+) U ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cT
    @0
    wcel
    #
    cU
    @0
    wcel
    #
    w3a
    #
    cU
    cS
    wss
    #
    wa
    #
    cS
    cU
    cT
    cG
    coppg
    cfv
    #
    clsm
    cfv
    #
    co
    #
    cin
    #
    cU
    cS
    cT
    cin
    #
    @8
    co
    #
    cS
    cT
    cU
    c.po
    co
    #
    cin
    @11
    cU
    c.po
    co
    @6
    @9
    cS
    cin
    #
    cU
    cT
    cS
    cin
    #
    @8
    co
    #
    @10
    @12
    @6
    @16
    @14
    @6
    cU
    @7
    csubg
    cfv
    #
    wcel
    cT
    @17
    wcel
    cS
    @17
    wcel
    @5
    @16
    @14
    wceq
    @6
    cU
    @0
    @17
    @1
    @2
    @3
    @5
    simpl3
    cG
    @7
    @7
    eqid
    #
    oppgsubg
    #
    syl6eleq
    @6
    cT
    @0
    @17
    @1
    @2
    @3
    @5
    simpl2
    @19
    syl6eleq
    @6
    cS
    @0
    @17
    @1
    @2
    @3
    @5
    simpl1
    @19
    syl6eleq
    @4
    @5
    simpr
    @8
    cU
    cT
    cS
    @7
    @8
    eqid
    lsmmod
    syl31anc
    eqcomd
    @9
    cS
    incom
    @15
    @11
    cU
    @8
    cT
    cS
    incom
    oveq2i
    3eqtr3g
    @9
    @13
    cS
    c.po
    cU
    cT
    cG
    @7
    @18
    lsmmod.p
    oppglsm
    ineq2i
    c.po
    cU
    @11
    cG
    @7
    @18
    lsmmod.p
    oppglsm
    3eqtr3g
end
