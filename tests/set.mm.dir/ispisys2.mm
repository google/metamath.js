include "wcel.mm"
include "cpw.mm"
include "cfi.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cint.mm"
include "cfn.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "ispisys.mm"
include "dfss3.mm"
include "cvv.mm"
include "wne.mm"
include "elex.mm"
include "adantr.mm"
include "simpr.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simpld.mm"
include "elin1d.mm"
include "elpwid.mm"
include "simprd.mm"
include "elin2d.mm"
include "elfir.mm"
include "syl13anc.mm"
include "wceq.mm"
include "wrex.mm"
include "elfi2.mm"
include "biimpa.mm"
include "eleq1d.mm"
include "ralxfrd.mm"
include "syl5bb.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem ispisys2
  let vx: setvar x
  let cP: class P
  let cS: class S
  let cO: class O
  let vs: setvar s
  let vt: setvar t
  let vy: setvar y
  assume ispisys.p: |- P = { s e. ~P ~P O | ( fi ` s ) C_ s }

  disjoint O s
  disjoint O x
  disjoint s x
  disjoint S s
  disjoint S x
  disjoint O t
  disjoint O y
  disjoint s t
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint S y
  disjoint P t
  assert |- ( S e. P <-> ( S e. ~P ~P O /\ A. x e. ( ( ~P S i^i Fin ) \ { (/) } ) |^| x e. S ) )

  proof
    cS
    cP
    wcel
    cS
    cO
    cpw
    cpw
    #
    wcel
    #
    cS
    cfi
    cfv
    #
    cS
    wss
    #
    wa
    @1
    vx
    cv
    #
    cint
    #
    cS
    wcel
    #
    vx
    cS
    cpw
    #
    cfn
    cin
    #
    c0
    csn
    cdif
    #
    wral
    #
    wa
    cP
    cS
    cO
    vs
    ispisys.p
    ispisys
    @1
    @3
    @10
    @3
    vy
    cv
    #
    cS
    wcel
    #
    vy
    @2
    wral
    @1
    @10
    vy
    @2
    cS
    dfss3
    @1
    @12
    @6
    vy
    vx
    @5
    @2
    @9
    @1
    @4
    @9
    wcel
    #
    wa
    #
    cS
    cvv
    wcel
    #
    @4
    cS
    wss
    @4
    c0
    wne
    #
    @4
    cfn
    wcel
    @5
    @2
    wcel
    @1
    @15
    @13
    cS
    @0
    elex
    adantr
    @14
    @4
    cS
    @14
    @7
    cfn
    @4
    @14
    @4
    @8
    wcel
    #
    @16
    @14
    @13
    @17
    @16
    wa
    @1
    @13
    simpr
    @4
    @8
    c0
    eldifsn
    sylib
    #
    simpld
    #
    elin1d
    elpwid
    @14
    @17
    @16
    @18
    simprd
    @14
    @7
    cfn
    @4
    @19
    elin2d
    @4
    cS
    cvv
    elfir
    syl13anc
    @1
    @11
    @2
    wcel
    @11
    @5
    wceq
    #
    vx
    @9
    wrex
    vx
    @11
    cS
    @0
    elfi2
    biimpa
    @1
    @20
    wa
    @11
    @5
    cS
    @1
    @20
    simpr
    eleq1d
    ralxfrd
    syl5bb
    pm5.32i
    bitri
end
