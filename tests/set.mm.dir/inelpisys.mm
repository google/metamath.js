include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "cint.mm"
include "cin.mm"
include "wceq.mm"
include "intprg.mm"
include "3adant1.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "inteq.mm"
include "eqidd.mm"
include "eleq12d.mm"
include "wral.mm"
include "ispisys2.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "wss.mm"
include "prssi.mm"
include "prex.mm"
include "elpw.mm"
include "sylibr.mm"
include "prfi.mm"
include "a1i.mm"
include "elind.mm"
include "wn.mm"
include "wne.mm"
include "prnzg.mm"
include "3ad2ant2.mm"
include "neneqd.mm"
include "elsni.mm"
include "con3i.mm"
include "syl.mm"
include "eldifd.mm"
include "rspcdva.mm"
include "eqeltrrd.mm"

theorem inelpisys
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cO: class O
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  assume ispisys.p: |- P = { s e. ~P ~P O | ( fi ` s ) C_ s }

  disjoint O s
  disjoint S s
  disjoint O t
  disjoint O x
  disjoint O y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint P t
  disjoint A x
  disjoint B x
  disjoint P x
  assert |- ( ( S e. P /\ A e. S /\ B e. S ) -> ( A i^i B ) e. S )

  proof
    cS
    cP
    wcel
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    w3a
    #
    cA
    cB
    cpr
    #
    cint
    #
    cA
    cB
    cin
    #
    cS
    @1
    @2
    @5
    @6
    wceq
    @0
    cA
    cB
    cS
    cS
    intprg
    3adant1
    @3
    vx
    cv
    #
    cint
    #
    cS
    wcel
    #
    @5
    cS
    wcel
    vx
    cS
    cpw
    #
    cfn
    cin
    #
    c0
    csn
    #
    cdif
    #
    @4
    @7
    @4
    wceq
    #
    @8
    @5
    cS
    cS
    @7
    @4
    inteq
    @14
    cS
    eqidd
    eleq12d
    @0
    @1
    @9
    vx
    @13
    wral
    #
    @2
    @0
    cS
    cO
    cpw
    cpw
    wcel
    @15
    vx
    cP
    cS
    cO
    vs
    ispisys.p
    ispisys2
    simprbi
    3ad2ant1
    @3
    @4
    @11
    @12
    @3
    @10
    cfn
    @4
    @1
    @2
    @4
    @10
    wcel
    #
    @0
    @1
    @2
    wa
    @4
    cS
    wss
    @16
    cA
    cB
    cS
    prssi
    @4
    cS
    cA
    cB
    prex
    elpw
    sylibr
    3adant1
    @4
    cfn
    wcel
    @3
    cA
    cB
    prfi
    a1i
    elind
    @3
    @4
    c0
    wceq
    #
    wn
    @4
    @12
    wcel
    #
    wn
    @3
    @4
    c0
    @1
    @0
    @4
    c0
    wne
    @2
    cA
    cB
    cS
    prnzg
    3ad2ant2
    neneqd
    @18
    @17
    @4
    c0
    elsni
    con3i
    syl
    eldifd
    rspcdva
    eqeltrrd
end
