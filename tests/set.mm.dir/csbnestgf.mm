include "wcel.mm"
include "wnfc.mm"
include "wal.mm"
include "wa.mm"
include "cv.mm"
include "csb.mm"
include "wsbc.mm"
include "cab.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "df-csb.mm"
include "abeq2i.mm"
include "sbcbii.mm"
include "wnf.mm"
include "wb.mm"
include "nfcr.mm"
include "alimi.mm"
include "sbcnestgf.mm"
include "sylan2.mm"
include "syl5bb.mm"
include "abbidv.mm"
include "sylan.mm"
include "3eqtr4g.mm"

theorem csbnestgf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vz: setvar z
  let wph: wff ph


  assert |- ( ( A e. V /\ A. y F/_ x C ) -> [_ A / x ]_ [_ B / y ]_ C = [_ [_ A / x ]_ B / y ]_ C )

  proof
    cA
    cV
    wcel
    #
    vx
    cC
    wnfc
    #
    vy
    wal
    #
    wa
    vz
    cv
    #
    vy
    cB
    cC
    csb
    #
    wcel
    #
    vx
    cA
    wsbc
    #
    vz
    cab
    #
    @3
    cC
    wcel
    #
    vy
    vx
    cA
    cB
    csb
    #
    wsbc
    #
    vz
    cab
    #
    vx
    cA
    @4
    csb
    vy
    @9
    cC
    csb
    @0
    cA
    cvv
    wcel
    #
    @2
    @7
    @11
    wceq
    cA
    cV
    elex
    @12
    @2
    wa
    #
    @6
    @10
    vz
    @6
    @8
    vy
    cB
    wsbc
    #
    vx
    cA
    wsbc
    #
    @13
    @10
    @5
    @14
    vx
    cA
    @14
    vz
    @4
    vy
    vz
    cB
    cC
    df-csb
    abeq2i
    sbcbii
    @2
    @12
    @8
    vx
    wnf
    #
    vy
    wal
    @15
    @10
    wb
    @1
    @16
    vy
    vx
    vz
    cC
    nfcr
    alimi
    @8
    vx
    vy
    cA
    cB
    cvv
    sbcnestgf
    sylan2
    syl5bb
    abbidv
    sylan
    vx
    vz
    cA
    @4
    df-csb
    vy
    vz
    @9
    cC
    df-csb
    3eqtr4g
end
