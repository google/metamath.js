include "cch.mm"
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
include "h0elch.mm"
include "ne0ii.mm"
include "pm3.2i.mm"
include "elimhyp.mm"
include "chintcli.mm"
include "dedth.mm"

theorem chintcl
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A C_ CH /\ A =/= (/) ) -> |^| A e. CH )

  proof
    cA
    cch
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
    cch
    wcel
    @2
    cA
    cch
    cif
    #
    cint
    #
    cch
    wcel
    cA
    cch
    cA
    @4
    wceq
    #
    @3
    @5
    cch
    cA
    @4
    inteq
    eleq1d
    @4
    @2
    @4
    cch
    wss
    #
    @4
    c0
    wne
    #
    wa
    cch
    cch
    wss
    #
    cch
    c0
    wne
    #
    wa
    cA
    cch
    @6
    @0
    @7
    @1
    @8
    cA
    @4
    cch
    sseq1
    cA
    @4
    c0
    neeq1
    anbi12d
    cch
    @4
    wceq
    @9
    @7
    @10
    @8
    cch
    @4
    cch
    sseq1
    cch
    @4
    c0
    neeq1
    anbi12d
    @9
    @10
    cch
    ssid
    c0h
    cch
    h0elch
    ne0ii
    pm3.2i
    elimhyp
    chintcli
    dedth
end
