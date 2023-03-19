include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cltr.mm"
include "wbr.mm"
include "wral.mm"
include "cnr.mm"
include "wrex.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "wss.mm"
include "ltrelsr.mm"
include "brel.mm"
include "simpld.mm"
include "ralimi.mm"
include "dfss3.mm"
include "sylibr.mm"
include "sseld.mm"
include "rexlimivw.mm"
include "impcom.mm"
include "c1r.mm"
include "cif.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "imbi1d.mm"
include "c1p.mm"
include "cop.mm"
include "cer.mm"
include "cec.mm"
include "cplr.mm"
include "co.mm"
include "cab.mm"
include "opeq1.mm"
include "eceq1d.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "cbvabv.mm"
include "1sr.mm"
include "elimel.mm"
include "supsrlem.mm"
include "dedth.mm"
include "mpcom.mm"
include "ex.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "imp.mm"

theorem supsr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint A w
  disjoint u v
  disjoint A v
  disjoint A u
  assert |- ( ( A =/= (/) /\ E. x e. R. A. y e. A y <R x ) -> E. x e. R. ( A. y e. A -. x <R y /\ A. y e. R. ( y <R x -> E. z e. A y <R z ) ) )

  proof
    cA
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cltr
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cnr
    wrex
    #
    @2
    @1
    cltr
    wbr
    wn
    vy
    cA
    wral
    @3
    @1
    vz
    cv
    cltr
    wbr
    vz
    cA
    wrex
    wi
    vy
    cnr
    wral
    wa
    vx
    cnr
    wrex
    #
    @0
    vu
    cv
    #
    cA
    wcel
    #
    vu
    wex
    @5
    @6
    wi
    #
    vu
    cA
    n0
    @8
    @9
    vu
    @8
    @5
    @6
    @7
    cnr
    wcel
    #
    @8
    @5
    wa
    #
    @6
    @5
    @8
    @10
    @4
    @8
    @10
    wi
    vx
    cnr
    @4
    cA
    cnr
    @7
    @4
    @1
    cnr
    wcel
    #
    vy
    cA
    wral
    cA
    cnr
    wss
    @3
    @12
    vy
    cA
    @3
    @12
    @2
    cnr
    wcel
    @1
    @2
    cnr
    cnr
    cltr
    ltrelsr
    brel
    simpld
    ralimi
    vy
    cA
    cnr
    dfss3
    sylibr
    sseld
    rexlimivw
    impcom
    @10
    @11
    @6
    wi
    @10
    @7
    c1r
    cif
    #
    cA
    wcel
    #
    @5
    wa
    #
    @6
    wi
    @7
    c1r
    @7
    @13
    wceq
    #
    @11
    @15
    @6
    @16
    @8
    @14
    @5
    @7
    @13
    cA
    eleq1
    anbi1d
    imbi1d
    vx
    vy
    vz
    vw
    cA
    @13
    vv
    cv
    #
    c1p
    cop
    #
    cer
    cec
    #
    cplr
    co
    #
    cA
    wcel
    #
    vv
    cab
    @13
    @21
    @13
    vw
    cv
    #
    c1p
    cop
    #
    cer
    cec
    #
    cplr
    co
    #
    cA
    wcel
    vv
    vw
    @17
    @22
    wceq
    #
    @20
    @25
    cA
    @26
    @19
    @24
    @13
    cplr
    @26
    @18
    @23
    cer
    @17
    @22
    c1p
    opeq1
    eceq1d
    oveq2d
    eleq1d
    cbvabv
    @7
    c1r
    cnr
    1sr
    elimel
    supsrlem
    dedth
    mpcom
    ex
    exlimiv
    sylbi
    imp
end
