include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "elxp.mm"
include "df-rex.mm"
include "an13.mm"
include "exbii.mm"
include "bitr4i.mm"
include "velsn.mm"
include "anbi1i.mm"
include "simpr.mm"
include "opeq1.mm"
include "adantr.mm"
include "eqtrd.mm"
include "sylbi.mm"
include "reximi.mm"
include "sylbir.mm"
include "eximi.mm"
include "19.9v.mm"
include "sylib.mm"
include "adantl.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "snidg.mm"
include "opelxp.mm"
include "biimpri.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "adantllr.mm"
include "r19.29af.mm"
include "impbida.mm"

theorem elsnxpOLD
  let vy: setvar y
  let cA: class A
  let cV: class V
  let cX: class X
  let cZ: class Z
  let vx: setvar x

  disjoint A y
  disjoint V y
  disjoint X y
  disjoint Z y
  disjoint A x
  disjoint x y
  disjoint X x
  disjoint Z x
  assert |- ( X e. V -> ( Z e. ( { X } X. A ) <-> E. y e. A Z = <. X , y >. ) )

  proof
    cX
    cV
    wcel
    #
    cZ
    cX
    csn
    #
    cA
    cxp
    #
    wcel
    #
    cZ
    cX
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    cA
    wrex
    #
    @3
    @7
    @0
    @3
    cZ
    vx
    cv
    #
    @4
    cop
    #
    wceq
    #
    @8
    @1
    wcel
    #
    @4
    cA
    wcel
    #
    wa
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    @7
    vx
    vy
    cZ
    @1
    cA
    elxp
    @15
    @7
    vx
    wex
    @7
    @14
    @7
    vx
    @14
    @11
    @10
    wa
    #
    vy
    cA
    wrex
    #
    @7
    @17
    @12
    @16
    wa
    #
    vy
    wex
    @14
    @16
    vy
    cA
    df-rex
    @13
    @18
    vy
    @10
    @11
    @12
    an13
    exbii
    bitr4i
    @16
    @6
    vy
    cA
    @16
    @8
    cX
    wceq
    #
    @10
    wa
    #
    @6
    @11
    @19
    @10
    vx
    cX
    velsn
    anbi1i
    @20
    cZ
    @9
    @5
    @19
    @10
    simpr
    @19
    @9
    @5
    wceq
    @10
    @8
    cX
    @4
    opeq1
    adantr
    eqtrd
    sylbi
    reximi
    sylbir
    eximi
    @7
    vx
    19.9v
    sylib
    sylbi
    adantl
    @0
    @7
    wa
    @6
    @3
    vy
    cA
    @0
    @7
    vy
    @0
    vy
    nfv
    @6
    vy
    cA
    nfre1
    nfan
    @0
    @12
    @6
    @3
    @7
    @0
    @12
    wa
    #
    @6
    wa
    cZ
    @5
    @2
    @21
    @6
    simpr
    @21
    @5
    @2
    wcel
    #
    @6
    @21
    cX
    @1
    wcel
    #
    @12
    @22
    @0
    @23
    @12
    cX
    cV
    snidg
    adantr
    @0
    @12
    simpr
    @22
    @23
    @12
    wa
    cX
    @4
    @1
    cA
    opelxp
    biimpri
    syl2anc
    adantr
    eqeltrd
    adantllr
    @0
    @7
    simpr
    r19.29af
    impbida
end
