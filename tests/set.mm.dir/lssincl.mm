include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "cint.mm"
include "cin.mm"
include "wceq.mm"
include "intprg.mm"
include "3adant1.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "simp1.mm"
include "prssi.mm"
include "prnzg.mm"
include "3ad2ant2.mm"
include "lssintcl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"

theorem lssincl
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume lssintcl.s: |- S = ( LSubSp ` W )


  assert |- ( ( W e. LMod /\ T e. S /\ U e. S ) -> ( T i^i U ) e. S )

  proof
    cW
    clmod
    wcel
    #
    cT
    cS
    wcel
    #
    cU
    cS
    wcel
    #
    w3a
    #
    cT
    cU
    cpr
    #
    cint
    #
    cT
    cU
    cin
    #
    cS
    @1
    @2
    @5
    @6
    wceq
    @0
    cT
    cU
    cS
    cS
    intprg
    3adant1
    @3
    @0
    @4
    cS
    wss
    #
    @4
    c0
    wne
    #
    @5
    cS
    wcel
    @0
    @1
    @2
    simp1
    @1
    @2
    @7
    @0
    cT
    cU
    cS
    prssi
    3adant1
    @1
    @0
    @8
    @2
    cT
    cU
    cS
    prnzg
    3ad2ant2
    @4
    cS
    cW
    lssintcl.s
    lssintcl
    syl3anc
    eqeltrrd
end
