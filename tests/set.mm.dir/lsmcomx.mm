include "cabl.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "sseldd.mm"
include "simpl3.mm"
include "simprr.mm"
include "eqid.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "eqeq2d.mm"
include "2rexbidva.mm"
include "rexcom.mm"
include "syl6bb.mm"
include "lsmelvalx.mm"
include "wb.mm"
include "3com23.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem lsmcomx
  let cB: class B
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lsmcomx.v: |- B = ( Base ` G )
  assume lsmcomx.s: |- .(+) = ( LSSum ` G )


  assert |- ( ( G e. Abel /\ T C_ B /\ U C_ B ) -> ( T .(+) U ) = ( U .(+) T ) )

  proof
    cG
    cabl
    wcel
    #
    cT
    cB
    wss
    #
    cU
    cB
    wss
    #
    w3a
    #
    vx
    cT
    cU
    c.po
    co
    #
    cU
    cT
    c.po
    co
    #
    @3
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vz
    cU
    wrex
    vy
    cT
    wrex
    #
    @6
    @8
    @7
    @9
    co
    #
    wceq
    #
    vy
    cT
    wrex
    vz
    cU
    wrex
    #
    @6
    @4
    wcel
    @6
    @5
    wcel
    #
    @3
    @12
    @14
    vz
    cU
    wrex
    vy
    cT
    wrex
    @15
    @3
    @11
    @14
    vy
    vz
    cT
    cU
    @3
    @7
    cT
    wcel
    #
    @8
    cU
    wcel
    #
    wa
    #
    wa
    #
    @10
    @13
    @6
    @20
    @0
    @7
    cB
    wcel
    @8
    cB
    wcel
    @10
    @13
    wceq
    @0
    @1
    @2
    @19
    simpl1
    @20
    cT
    cB
    @7
    @0
    @1
    @2
    @19
    simpl2
    @3
    @17
    @18
    simprl
    sseldd
    @20
    cU
    cB
    @8
    @0
    @1
    @2
    @19
    simpl3
    @3
    @17
    @18
    simprr
    sseldd
    cB
    @9
    cG
    @7
    @8
    lsmcomx.v
    @9
    eqid
    #
    ablcom
    syl3anc
    eqeq2d
    2rexbidva
    @14
    vy
    vz
    cT
    cU
    rexcom
    syl6bb
    vy
    vz
    cB
    @9
    c.po
    cT
    cU
    cG
    cabl
    @6
    lsmcomx.v
    @21
    lsmcomx.s
    lsmelvalx
    @0
    @2
    @1
    @16
    @15
    wb
    vz
    vy
    cB
    @9
    c.po
    cU
    cT
    cG
    cabl
    @6
    lsmcomx.v
    @21
    lsmcomx.s
    lsmelvalx
    3com23
    3bitr4d
    eqrdv
end
