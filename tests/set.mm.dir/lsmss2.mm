include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "wa.mm"
include "ssid.mm"
include "wb.mm"
include "lsmlub.mm"
include "3anidm13.mm"
include "biimpd.mm"
include "mpani.mm"
include "3impia.mm"
include "lsmub1.mm"
include "3adant3.mm"
include "eqssd.mm"

theorem lsmss2
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let va: setvar a
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let cR: class R
  assume lsmub1.p: |- .(+) = ( LSSum ` G )


  assert |- ( ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) /\ U C_ T ) -> ( T .(+) U ) = T )

  proof
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @0
    wcel
    #
    cU
    cT
    wss
    #
    w3a
    cT
    cU
    c.po
    co
    #
    cT
    @1
    @2
    @3
    @4
    cT
    wss
    #
    @1
    @2
    wa
    #
    cT
    cT
    wss
    #
    @3
    @5
    cT
    ssid
    @6
    @7
    @3
    wa
    #
    @5
    @1
    @2
    @8
    @5
    wb
    c.po
    cT
    cU
    cT
    cG
    lsmub1.p
    lsmlub
    3anidm13
    biimpd
    mpani
    3impia
    @1
    @2
    cT
    @4
    wss
    @3
    c.po
    cT
    cU
    cG
    lsmub1.p
    lsmub1
    3adant3
    eqssd
end
