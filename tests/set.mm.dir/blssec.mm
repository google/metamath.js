include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "cbl.mm"
include "co.mm"
include "cpnf.mm"
include "cec.mm"
include "wss.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "pnfge.mm"
include "adantl.mm"
include "wi.mm"
include "pnfxr.mm"
include "ssbl.mm"
include "3expia.mm"
include "mpanr2.mm"
include "mpd.mm"
include "3impa.mm"
include "wceq.mm"
include "xmetec.mm"
include "3adant3.mm"
include "sseqtr4d.mm"

theorem blssec
  let cD: class D
  let cP: class P
  let c.sm: class .~
  let cS: class S
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xmeter.1: |- .~ = ( `' D " RR )


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ S e. RR* ) -> ( P ( ball ` D ) S ) C_ [ P ] .~ )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cS
    cxr
    wcel
    #
    w3a
    cP
    cS
    cD
    cbl
    cfv
    #
    co
    #
    cP
    cpnf
    @3
    co
    #
    cP
    c.sm
    cec
    #
    @0
    @1
    @2
    @4
    @5
    wss
    #
    @0
    @1
    wa
    #
    @2
    wa
    cS
    cpnf
    cle
    wbr
    #
    @7
    @2
    @9
    @8
    cS
    pnfge
    adantl
    @8
    @2
    cpnf
    cxr
    wcel
    #
    @9
    @7
    wi
    pnfxr
    @8
    @2
    @10
    wa
    @9
    @7
    cD
    cP
    cS
    cpnf
    cX
    ssbl
    3expia
    mpanr2
    mpd
    3impa
    @0
    @1
    @6
    @5
    wceq
    @2
    cD
    cP
    c.sm
    cX
    xmeter.1
    xmetec
    3adant3
    sseqtr4d
end
