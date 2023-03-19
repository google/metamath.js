include "chil.mm"
include "cort.mm"
include "cfv.mm"
include "c0h.mm"
include "cv.mm"
include "wcel.mm"
include "c0v.mm"
include "wceq.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wral.mm"
include "csh.mm"
include "wa.mm"
include "wb.mm"
include "helsh.mm"
include "shocel.mm"
include "ax-mp.mm"
include "simprbi.mm"
include "wss.mm"
include "shocss.mm"
include "sseli.mm"
include "hial0.mm"
include "syl.mm"
include "mpbid.mm"
include "elch0.mm"
include "sylibr.mm"
include "ssriv.mm"
include "h0elsh.mm"
include "shococss.mm"
include "choc0.mm"
include "fveq2i.mm"
include "sseqtri.mm"
include "eqssi.mm"

theorem choc1
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( _|_ ` ~H ) = 0H

  proof
    chil
    cort
    cfv
    #
    c0h
    vx
    @0
    c0h
    vx
    cv
    #
    @0
    wcel
    #
    @1
    c0v
    wceq
    #
    @1
    c0h
    wcel
    @2
    @1
    vy
    cv
    csp
    co
    cc0
    wceq
    vy
    chil
    wral
    #
    @3
    @2
    @1
    chil
    wcel
    #
    @4
    chil
    csh
    wcel
    #
    @2
    @5
    @4
    wa
    wb
    helsh
    vy
    @1
    chil
    shocel
    ax-mp
    simprbi
    @2
    @5
    @4
    @3
    wb
    @0
    chil
    @1
    @6
    @0
    chil
    wss
    helsh
    chil
    shocss
    ax-mp
    sseli
    vy
    @1
    hial0
    syl
    mpbid
    @1
    elch0
    sylibr
    ssriv
    c0h
    c0h
    cort
    cfv
    #
    cort
    cfv
    #
    @0
    c0h
    csh
    wcel
    c0h
    @8
    wss
    h0elsh
    c0h
    shococss
    ax-mp
    @7
    chil
    cort
    choc0
    fveq2i
    sseqtri
    eqssi
end
