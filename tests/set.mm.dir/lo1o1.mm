include "cc.mm"
include "wf.mm"
include "cr.mm"
include "wss.mm"
include "co1.mm"
include "wcel.mm"
include "cabs.mm"
include "ccom.mm"
include "clo1.mm"
include "cdm.mm"
include "o1dm.mm"
include "fdm.mm"
include "sseq1d.mm"
include "syl5ib.mm"
include "lo1dm.mm"
include "wceq.mm"
include "absf.mm"
include "fco.mm"
include "mpan.mm"
include "syl.mm"
include "wb.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "fvco3.mm"
include "adantlr.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "2rexbidv.mm"
include "ello12.mm"
include "sylan.mm"
include "elo12.mm"
include "3bitr4rd.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem lo1o1
  let cA: class A
  let cF: class F
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let vf: setvar f
  let cM: class M


  assert |- ( F : A --> CC -> ( F e. O(1) <-> ( abs o. F ) e. <_O(1) ) )

  proof
    cA
    cc
    cF
    wf
    #
    cA
    cr
    wss
    #
    cF
    co1
    wcel
    #
    cabs
    cF
    ccom
    #
    clo1
    wcel
    #
    @2
    cF
    cdm
    #
    cr
    wss
    @0
    @1
    cF
    o1dm
    @0
    @5
    cA
    cr
    cA
    cc
    cF
    fdm
    sseq1d
    syl5ib
    @4
    @3
    cdm
    #
    cr
    wss
    @0
    @1
    @3
    lo1dm
    @0
    @6
    cA
    cr
    @0
    cA
    cr
    @3
    wf
    #
    @6
    cA
    wceq
    cc
    cr
    cabs
    wf
    @0
    @7
    absf
    cA
    cc
    cr
    cabs
    cF
    fco
    mpan
    #
    cA
    cr
    @3
    fdm
    syl
    sseq1d
    syl5ib
    @0
    @1
    @2
    @4
    wb
    @0
    @1
    wa
    #
    vx
    cv
    vy
    cv
    #
    cle
    wbr
    #
    @10
    @3
    cfv
    #
    vm
    cv
    #
    cle
    wbr
    #
    wi
    #
    vy
    cA
    wral
    #
    vm
    cr
    wrex
    vx
    cr
    wrex
    #
    @11
    @10
    cF
    cfv
    cabs
    cfv
    #
    @13
    cle
    wbr
    #
    wi
    #
    vy
    cA
    wral
    #
    vm
    cr
    wrex
    vx
    cr
    wrex
    @4
    @2
    @9
    @16
    @21
    vx
    vm
    cr
    cr
    @9
    @15
    @20
    vy
    cA
    @9
    @10
    cA
    wcel
    #
    wa
    #
    @14
    @19
    @11
    @23
    @12
    @18
    @13
    cle
    @0
    @22
    @12
    @18
    wceq
    @1
    cA
    cc
    @10
    cabs
    cF
    fvco3
    adantlr
    breq1d
    imbi2d
    ralbidva
    2rexbidv
    @0
    @7
    @1
    @4
    @17
    wb
    @8
    vx
    vy
    cA
    vm
    @3
    ello12
    sylan
    vx
    vy
    cA
    vm
    cF
    elo12
    3bitr4rd
    ex
    pm5.21ndd
end
