include "wrel.mm"
include "cdm.mm"
include "wa.mm"
include "ctpos.mm"
include "cvv.mm"
include "cxp.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cin.mm"
include "tpostpos.mm"
include "wss.mm"
include "wceq.mm"
include "relrelss.mm"
include "ssun1.mm"
include "xpss1.mm"
include "ax-mp.mm"
include "sstr.mm"
include "mpan2.mm"
include "sylbi.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"

theorem tpostpos2
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( ( Rel F /\ Rel dom F ) -> tpos tpos F = F )

  proof
    cF
    wrel
    cF
    cdm
    wrel
    wa
    #
    cF
    ctpos
    ctpos
    cF
    cvv
    cvv
    cxp
    #
    c0
    csn
    #
    cun
    #
    cvv
    cxp
    #
    cin
    #
    cF
    cF
    tpostpos
    @0
    cF
    @4
    wss
    #
    @5
    cF
    wceq
    @0
    cF
    @1
    cvv
    cxp
    #
    wss
    #
    @6
    cF
    relrelss
    @8
    @7
    @4
    wss
    #
    @6
    @1
    @3
    wss
    @9
    @1
    @2
    ssun1
    @1
    @3
    cvv
    xpss1
    ax-mp
    cF
    @7
    @4
    sstr
    mpan2
    sylbi
    cF
    @4
    df-ss
    sylib
    syl5eq
end
