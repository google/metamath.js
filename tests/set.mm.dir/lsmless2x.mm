include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "ssrexv.mm"
include "reximdv.mm"
include "adantl.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "simpl3.mm"
include "sstrd.mm"
include "eqid.mm"
include "lsmelvalx.mm"
include "syl3anc.mm"
include "adantr.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem lsmless2x
  let cB: class B
  let c.po: class .(+)
  let cR: class R
  let cT: class T
  let cU: class U
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lsmless2.v: |- B = ( Base ` G )
  assume lsmless2.s: |- .(+) = ( LSSum ` G )


  assert |- ( ( ( G e. V /\ R C_ B /\ U C_ B ) /\ T C_ U ) -> ( R .(+) T ) C_ ( R .(+) U ) )

  proof
    cG
    cV
    wcel
    #
    cR
    cB
    wss
    #
    cU
    cB
    wss
    #
    w3a
    #
    cT
    cU
    wss
    #
    wa
    #
    vx
    cR
    cT
    c.po
    co
    #
    cR
    cU
    c.po
    co
    #
    @5
    vx
    cv
    #
    vy
    cv
    vz
    cv
    cG
    cplusg
    cfv
    #
    co
    wceq
    #
    vz
    cT
    wrex
    #
    vy
    cR
    wrex
    #
    @10
    vz
    cU
    wrex
    #
    vy
    cR
    wrex
    #
    @8
    @6
    wcel
    #
    @8
    @7
    wcel
    #
    @4
    @12
    @14
    wi
    @3
    @4
    @11
    @13
    vy
    cR
    @10
    vz
    cT
    cU
    ssrexv
    reximdv
    adantl
    @5
    @0
    @1
    cT
    cB
    wss
    @15
    @12
    wb
    @0
    @1
    @2
    @4
    simpl1
    @0
    @1
    @2
    @4
    simpl2
    @5
    cT
    cU
    cB
    @3
    @4
    simpr
    @0
    @1
    @2
    @4
    simpl3
    sstrd
    vy
    vz
    cB
    @9
    c.po
    cR
    cT
    cG
    cV
    @8
    lsmless2.v
    @9
    eqid
    #
    lsmless2.s
    lsmelvalx
    syl3anc
    @3
    @16
    @14
    wb
    @4
    vy
    vz
    cB
    @9
    c.po
    cR
    cU
    cG
    cV
    @8
    lsmless2.v
    @17
    lsmless2.s
    lsmelvalx
    adantr
    3imtr4d
    ssrdv
end
