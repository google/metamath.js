include "csh.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cint.mm"
include "wcel.mm"
include "cif.mm"
include "wceq.mm"
include "inteq.mm"
include "eleq1d.mm"
include "sseq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "ssid.mm"
include "c0h.mm"
include "h0elsh.mm"
include "ne0ii.mm"
include "pm3.2i.mm"
include "elimhyp.mm"
include "shintcli.mm"
include "dedth.mm"

theorem shintcl
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A C_ SH /\ A =/= (/) ) -> |^| A e. SH )

  proof
    cA
    csh
    wss
    #
    cA
    c0
    wne
    #
    wa
    #
    cA
    cint
    #
    csh
    wcel
    @2
    cA
    csh
    cif
    #
    cint
    #
    csh
    wcel
    cA
    csh
    cA
    @4
    wceq
    #
    @3
    @5
    csh
    cA
    @4
    inteq
    eleq1d
    @4
    @2
    @4
    csh
    wss
    #
    @4
    c0
    wne
    #
    wa
    csh
    csh
    wss
    #
    csh
    c0
    wne
    #
    wa
    cA
    csh
    @6
    @0
    @7
    @1
    @8
    cA
    @4
    csh
    sseq1
    cA
    @4
    c0
    neeq1
    anbi12d
    csh
    @4
    wceq
    @9
    @7
    @10
    @8
    csh
    @4
    csh
    sseq1
    csh
    @4
    c0
    neeq1
    anbi12d
    @9
    @10
    csh
    ssid
    c0h
    csh
    h0elsh
    ne0ii
    pm3.2i
    elimhyp
    shintcli
    dedth
end
