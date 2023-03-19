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
include "3anidm23.mm"
include "biimpd.mm"
include "mpan2i.mm"
include "3impia.mm"
include "lsmub2.mm"
include "3adant3.mm"
include "eqssd.mm"

theorem lsmss1
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


  assert |- ( ( T e. ( SubGrp ` G ) /\ U e. ( SubGrp ` G ) /\ T C_ U ) -> ( T .(+) U ) = U )

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
    cT
    cU
    wss
    #
    w3a
    cT
    cU
    c.po
    co
    #
    cU
    @1
    @2
    @3
    @4
    cU
    wss
    #
    @1
    @2
    wa
    #
    @3
    cU
    cU
    wss
    #
    @5
    cU
    ssid
    @6
    @3
    @7
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
    cU
    cG
    lsmub1.p
    lsmlub
    3anidm23
    biimpd
    mpan2i
    3impia
    @1
    @2
    cU
    @4
    wss
    @3
    c.po
    cT
    cU
    cG
    lsmub1.p
    lsmub2
    3adant3
    eqssd
end
