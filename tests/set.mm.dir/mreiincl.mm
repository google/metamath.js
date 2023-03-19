include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "w3a.mm"
include "ciin.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cint.mm"
include "dfiin2g.mm"
include "3ad2ant3.mm"
include "wss.mm"
include "simp1.mm"
include "uniiunlem.mm"
include "ibi.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "nfra1.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfcv.mm"
include "nfne.mm"
include "nfim.mm"
include "rsp.mm"
include "com12.mm"
include "elisset.mm"
include "rspe.mm"
include "ex.mm"
include "syl5.mm"
include "rexcom4.mm"
include "syl6ib.mm"
include "syld.mm"
include "abn0.mm"
include "syl6ibr.mm"
include "exlimi.mm"
include "sylbi.mm"
include "imp.mm"
include "3adant1.mm"
include "mreintcl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem mreiincl
  let vy: setvar y
  let cC: class C
  let cS: class S
  let cI: class I
  let cX: class X
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x

  disjoint I y
  disjoint X y
  disjoint C y
  disjoint C c
  disjoint C s
  disjoint C x
  disjoint c s
  disjoint c x
  disjoint s x
  disjoint X c
  disjoint X s
  disjoint X x
  disjoint S c
  disjoint S s
  disjoint S x
  disjoint I s
  disjoint s y
  assert |- ( ( C e. ( Moore ` X ) /\ I =/= (/) /\ A. y e. I S e. C ) -> |^|_ y e. I S e. C )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cI
    c0
    wne
    #
    cS
    cC
    wcel
    #
    vy
    cI
    wral
    #
    w3a
    #
    vy
    cI
    cS
    ciin
    #
    vs
    cv
    cS
    wceq
    #
    vy
    cI
    wrex
    #
    vs
    cab
    #
    cint
    #
    cC
    @3
    @0
    @5
    @9
    wceq
    @1
    vy
    vs
    cI
    cS
    cC
    dfiin2g
    3ad2ant3
    @4
    @0
    @8
    cC
    wss
    #
    @8
    c0
    wne
    #
    @9
    cC
    wcel
    @0
    @1
    @3
    simp1
    @3
    @0
    @10
    @1
    @3
    @10
    vy
    vs
    cI
    cS
    cC
    cC
    uniiunlem
    ibi
    3ad2ant3
    @1
    @3
    @11
    @0
    @1
    @3
    @11
    @1
    vy
    cv
    cI
    wcel
    #
    vy
    wex
    @3
    @11
    wi
    #
    vy
    cI
    n0
    @12
    @13
    vy
    @3
    @11
    vy
    @2
    vy
    cI
    nfra1
    vy
    @8
    c0
    @7
    vy
    vs
    @6
    vy
    cI
    nfre1
    nfab
    vy
    c0
    nfcv
    nfne
    nfim
    @12
    @3
    @7
    vs
    wex
    #
    @11
    @12
    @3
    @2
    @14
    @3
    @12
    @2
    @2
    vy
    cI
    rsp
    com12
    @12
    @2
    @6
    vs
    wex
    #
    vy
    cI
    wrex
    #
    @14
    @2
    @15
    @12
    @16
    vs
    cS
    cC
    elisset
    @12
    @15
    @16
    @15
    vy
    cI
    rspe
    ex
    syl5
    @6
    vy
    vs
    cI
    rexcom4
    syl6ib
    syld
    @7
    vs
    abn0
    syl6ibr
    exlimi
    sylbi
    imp
    3adant1
    cC
    @8
    cX
    mreintcl
    syl3anc
    eqeltrd
end
