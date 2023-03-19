include "wcel.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "csn.mm"
include "cint.mm"
include "vex.mm"
include "intsn.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "simpl.mm"
include "simpr.mm"
include "snssd.mm"
include "snnz.mm"
include "a1i.mm"
include "snfi.mm"
include "elfir.mm"
include "syl13anc.mm"
include "syl5eqelr.mm"
include "ex.mm"
include "ssrdv.mm"

theorem ssfii
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> A C_ ( fi ` A ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cA
    cfi
    cfv
    #
    @0
    vx
    cv
    #
    cA
    wcel
    #
    @2
    @1
    wcel
    @0
    @3
    wa
    #
    @2
    @2
    csn
    #
    cint
    #
    @1
    @2
    vx
    vex
    #
    intsn
    @4
    @0
    @5
    cA
    wss
    @5
    c0
    wne
    #
    @5
    cfn
    wcel
    #
    @6
    @1
    wcel
    @0
    @3
    simpl
    @4
    @2
    cA
    @0
    @3
    simpr
    snssd
    @8
    @4
    @2
    @7
    snnz
    a1i
    @9
    @4
    @2
    snfi
    a1i
    @5
    cA
    cV
    elfir
    syl13anc
    syl5eqelr
    ex
    ssrdv
end
