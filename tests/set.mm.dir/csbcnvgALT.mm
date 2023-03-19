include "wcel.mm"
include "csb.mm"
include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "wsbc.mm"
include "sbcbr123.mm"
include "csbconstg.mm"
include "breq12d.mm"
include "syl5bb.mm"
include "opabbidv.mm"
include "csbopabgALT.mm"
include "wceq.mm"
include "df-cnv.mm"
include "a1i.mm"
include "3eqtr4rd.mm"
include "csbeq2i.mm"
include "syl6eqr.mm"

theorem csbcnvgALT
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. V -> `' [_ A / x ]_ F = [_ A / x ]_ `' F )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cF
    csb
    #
    ccnv
    #
    vx
    cA
    vz
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    vy
    vz
    copab
    #
    csb
    #
    vx
    cA
    cF
    ccnv
    #
    csb
    @0
    @5
    vx
    cA
    wsbc
    #
    vy
    vz
    copab
    @3
    @4
    @1
    wbr
    #
    vy
    vz
    copab
    #
    @7
    @2
    @0
    @9
    @10
    vy
    vz
    @9
    vx
    cA
    @3
    csb
    #
    vx
    cA
    @4
    csb
    #
    @1
    wbr
    @0
    @10
    vx
    cA
    @3
    @4
    cF
    sbcbr123
    @0
    @12
    @3
    @13
    @4
    @1
    vx
    cA
    @3
    cV
    csbconstg
    vx
    cA
    @4
    cV
    csbconstg
    breq12d
    syl5bb
    opabbidv
    @5
    vx
    vy
    vz
    cA
    cV
    csbopabgALT
    @2
    @11
    wceq
    @0
    vy
    vz
    @1
    df-cnv
    a1i
    3eqtr4rd
    vx
    cA
    @8
    @6
    vy
    vz
    cF
    df-cnv
    csbeq2i
    syl6eqr
end
