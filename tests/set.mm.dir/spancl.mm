include "chil.mm"
include "wss.mm"
include "cspn.mm"
include "cfv.mm"
include "cv.mm"
include "csh.mm"
include "crab.mm"
include "cint.mm"
include "spanval.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "ssrab2.mm"
include "wrex.mm"
include "helsh.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mpan.mm"
include "rabn0.mm"
include "sylibr.mm"
include "shintcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem spancl
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ ~H -> ( span ` A ) e. SH )

  proof
    cA
    chil
    wss
    #
    cA
    cspn
    cfv
    cA
    vx
    cv
    #
    wss
    #
    vx
    csh
    crab
    #
    cint
    #
    csh
    vx
    cA
    spanval
    @0
    @3
    csh
    wss
    @3
    c0
    wne
    #
    @4
    csh
    wcel
    @2
    vx
    csh
    ssrab2
    @0
    @2
    vx
    csh
    wrex
    #
    @5
    chil
    csh
    wcel
    @0
    @6
    helsh
    @2
    @0
    vx
    chil
    csh
    @1
    chil
    cA
    sseq2
    rspcev
    mpan
    @2
    vx
    csh
    rabn0
    sylibr
    @3
    shintcl
    sylancr
    eqeltrd
end
