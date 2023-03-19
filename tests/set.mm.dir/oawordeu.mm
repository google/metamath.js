include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "wreu.mm"
include "wi.mm"
include "c0.mm"
include "cif.mm"
include "sseq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "reubidv.mm"
include "imbi12d.mm"
include "sseq2.mm"
include "eqeq2.mm"
include "crab.mm"
include "0elon.mm"
include "elimel.mm"
include "eqid.mm"
include "oawordeulem.mm"
include "dedth2h.mm"
include "imp.mm"

theorem oawordeu
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( ( A e. On /\ B e. On ) /\ A C_ B ) -> E! x e. On ( A +o x ) = B )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    cA
    cB
    wss
    #
    cA
    vx
    cv
    #
    coa
    co
    #
    cB
    wceq
    #
    vx
    con0
    wreu
    #
    @0
    @1
    @2
    @6
    wi
    @0
    cA
    c0
    cif
    #
    cB
    wss
    #
    @7
    @3
    coa
    co
    #
    cB
    wceq
    #
    vx
    con0
    wreu
    #
    wi
    @7
    @1
    cB
    c0
    cif
    #
    wss
    #
    @9
    @12
    wceq
    #
    vx
    con0
    wreu
    #
    wi
    cA
    cB
    c0
    c0
    cA
    @7
    wceq
    #
    @2
    @8
    @6
    @11
    cA
    @7
    cB
    sseq1
    @16
    @5
    @10
    vx
    con0
    @16
    @4
    @9
    cB
    cA
    @7
    @3
    coa
    oveq1
    eqeq1d
    reubidv
    imbi12d
    cB
    @12
    wceq
    #
    @8
    @13
    @11
    @15
    cB
    @12
    @7
    sseq2
    @17
    @10
    @14
    vx
    con0
    cB
    @12
    @9
    eqeq2
    reubidv
    imbi12d
    vx
    vy
    @7
    @12
    @12
    @7
    vy
    cv
    coa
    co
    wss
    vy
    con0
    crab
    #
    cA
    c0
    con0
    0elon
    elimel
    cB
    c0
    con0
    0elon
    elimel
    @18
    eqid
    oawordeulem
    dedth2h
    imp
end
