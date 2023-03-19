include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cuni.mm"
include "cin.mm"
include "wceq.mm"
include "simpr.mm"
include "sseqin2.mm"
include "sylib.mm"
include "cvv.mm"
include "simpl.mm"
include "id.mm"
include "filtop.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "adantr.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "elssuni.mm"
include "syl.mm"
include "cpw.mm"
include "restsspw.mm"
include "sspwuni.mm"
include "mpbi.mm"
include "a1i.mm"
include "eqssd.mm"

theorem trfil1
  let cA: class A
  let cL: class L
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( L e. ( Fil ` Y ) /\ A C_ Y ) -> A = U. ( L |`t A ) )

  proof
    cL
    cY
    cfil
    cfv
    #
    wcel
    #
    cA
    cY
    wss
    #
    wa
    #
    cA
    cL
    cA
    crest
    co
    #
    cuni
    #
    @3
    cA
    @4
    wcel
    cA
    @5
    wss
    @3
    cY
    cA
    cin
    #
    cA
    @4
    @3
    @2
    @6
    cA
    wceq
    @1
    @2
    simpr
    cA
    cY
    sseqin2
    sylib
    @3
    @1
    cA
    cvv
    wcel
    #
    cY
    cL
    wcel
    #
    @6
    @4
    wcel
    @1
    @2
    simpl
    @2
    @2
    @8
    @7
    @1
    @2
    id
    cL
    cY
    filtop
    #
    cA
    cY
    cL
    ssexg
    syl2anr
    @1
    @8
    @2
    @9
    adantr
    cY
    cA
    cL
    @0
    cvv
    elrestr
    syl3anc
    eqeltrrd
    cA
    @4
    elssuni
    syl
    @5
    cA
    wss
    #
    @3
    @4
    cA
    cpw
    wss
    @10
    cA
    cL
    restsspw
    @4
    cA
    sspwuni
    mpbi
    a1i
    eqssd
end
