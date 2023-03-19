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
include "adantl.mm"
include "wb.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl2.mm"
include "sstrd.mm"
include "simpl3.mm"
include "eqid.mm"
include "lsmelvalx.mm"
include "syl3anc.mm"
include "adantr.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem lsmless1x
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


  assert |- ( ( ( G e. V /\ T C_ B /\ U C_ B ) /\ R C_ T ) -> ( R .(+) U ) C_ ( T .(+) U ) )

  proof
    cG
    cV
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
    cR
    cT
    wss
    #
    wa
    #
    vx
    cR
    cU
    c.po
    co
    #
    cT
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
    vz
    cU
    wrex
    #
    vy
    cR
    wrex
    #
    @10
    vy
    cT
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
    @11
    @12
    wi
    @3
    @10
    vy
    cR
    cT
    ssrexv
    adantl
    @5
    @0
    cR
    cB
    wss
    @2
    @13
    @11
    wb
    @0
    @1
    @2
    @4
    simpl1
    @5
    cR
    cT
    cB
    @3
    @4
    simpr
    @0
    @1
    @2
    @4
    simpl2
    sstrd
    @0
    @1
    @2
    @4
    simpl3
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
    @9
    eqid
    #
    lsmless2.s
    lsmelvalx
    syl3anc
    @3
    @14
    @12
    wb
    @4
    vy
    vz
    cB
    @9
    c.po
    cT
    cU
    cG
    cV
    @8
    lsmless2.v
    @15
    lsmless2.s
    lsmelvalx
    adantr
    3imtr4d
    ssrdv
end
