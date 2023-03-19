include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "wn.mm"
include "clp.mm"
include "wi.mm"
include "cun.mm"
include "clslp.mm"
include "eleq2d.mm"
include "wo.mm"
include "elun.mm"
include "df-or.mm"
include "bitri.mm"
include "syl6bb.mm"
include "biimpd.mm"
include "imp32.mm"

theorem islpi
  let cP: class P
  let cS: class S
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume lpfval.1: |- X = U. J


  assert |- ( ( ( J e. Top /\ S C_ X ) /\ ( P e. ( ( cls ` J ) ` S ) /\ -. P e. S ) ) -> P e. ( ( limPt ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    cS
    cX
    wss
    wa
    #
    cP
    cS
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    cP
    cS
    wcel
    #
    wn
    #
    cP
    cS
    cJ
    clp
    cfv
    cfv
    #
    wcel
    #
    @0
    @2
    @4
    @6
    wi
    #
    @0
    @2
    cP
    cS
    @5
    cun
    #
    wcel
    #
    @7
    @0
    @1
    @8
    cP
    cS
    cJ
    cX
    lpfval.1
    clslp
    eleq2d
    @9
    @3
    @6
    wo
    @7
    cP
    cS
    @5
    elun
    @3
    @6
    df-or
    bitri
    syl6bb
    biimpd
    imp32
end
