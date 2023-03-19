include "wfn.mm"
include "wa.mm"
include "cdif.mm"
include "cdm.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "wss.mm"
include "wceq.mm"
include "difss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "fndm.mm"
include "adantr.mm"
include "syl5sseq.mm"
include "sseqin2.mm"
include "sylib.mm"
include "wcel.mm"
include "wbr.mm"
include "wex.mm"
include "vex.mm"
include "eldm.mm"
include "wn.mm"
include "wb.mm"
include "eqcom.mm"
include "fnbrfvb.mm"
include "syl5bb.mm"
include "adantll.mm"
include "necon3abid.mm"
include "fvex.mm"
include "breq2.mm"
include "notbid.mm"
include "ceqsexv.mm"
include "syl6bbr.mm"
include "adantlr.mm"
include "anbi1d.mm"
include "brdif.mm"
include "exbidv.mm"
include "bitr2d.mm"
include "rabbi2dva.mm"
include "eqtr3d.mm"

theorem fndmdif
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let vy: setvar y

  disjoint F x
  disjoint G x
  disjoint A x
  disjoint F y
  disjoint x y
  disjoint G y
  disjoint A y
  assert |- ( ( F Fn A /\ G Fn A ) -> dom ( F \ G ) = { x e. A | ( F ` x ) =/= ( G ` x ) } )

  proof
    cF
    cA
    wfn
    #
    cG
    cA
    wfn
    #
    wa
    #
    cA
    cF
    cG
    cdif
    #
    cdm
    #
    cin
    #
    @4
    vx
    cv
    #
    cF
    cfv
    #
    @6
    cG
    cfv
    #
    wne
    #
    vx
    cA
    crab
    @2
    @4
    cA
    wss
    @5
    @4
    wceq
    @2
    cF
    cdm
    #
    @4
    cA
    @3
    cF
    wss
    @4
    @10
    wss
    cF
    cG
    difss
    @3
    cF
    dmss
    ax-mp
    @0
    @10
    cA
    wceq
    @1
    cA
    cF
    fndm
    adantr
    syl5sseq
    @4
    cA
    sseqin2
    sylib
    @2
    @9
    vx
    cA
    @4
    @6
    @4
    wcel
    @6
    vy
    cv
    #
    @3
    wbr
    #
    vy
    wex
    #
    @2
    @6
    cA
    wcel
    #
    wa
    #
    @9
    vy
    @6
    @3
    vx
    vex
    eldm
    @15
    @9
    @11
    @7
    wceq
    #
    @6
    @11
    cG
    wbr
    #
    wn
    #
    wa
    #
    vy
    wex
    #
    @13
    @15
    @9
    @6
    @7
    cG
    wbr
    #
    wn
    #
    @20
    @15
    @21
    @7
    @8
    @1
    @14
    @7
    @8
    wceq
    #
    @21
    wb
    @0
    @23
    @8
    @7
    wceq
    @1
    @14
    wa
    @21
    @7
    @8
    eqcom
    cA
    @6
    @7
    cG
    fnbrfvb
    syl5bb
    adantll
    necon3abid
    @18
    @22
    vy
    @7
    @6
    cF
    fvex
    @16
    @17
    @21
    @11
    @7
    @6
    cG
    breq2
    notbid
    ceqsexv
    syl6bbr
    @15
    @19
    @12
    vy
    @15
    @19
    @6
    @11
    cF
    wbr
    #
    @18
    wa
    @12
    @15
    @16
    @24
    @18
    @0
    @14
    @16
    @24
    wb
    @1
    @16
    @7
    @11
    wceq
    @0
    @14
    wa
    @24
    @11
    @7
    eqcom
    cA
    @6
    @11
    cF
    fnbrfvb
    syl5bb
    adantlr
    anbi1d
    @6
    @11
    cF
    cG
    brdif
    syl6bbr
    exbidv
    bitr2d
    syl5bb
    rabbi2dva
    eqtr3d
end
