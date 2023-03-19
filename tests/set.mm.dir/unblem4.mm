include "com.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wf.mm"
include "cfv.mm"
include "csuc.mm"
include "wf1.mm"
include "omsson.mm"
include "sstr.mm"
include "mpan2.mm"
include "adantr.mm"
include "wfn.mm"
include "cvv.mm"
include "cdif.mm"
include "cint.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "unblem2.mm"
include "ralrimiv.mm"
include "ffnfv.mm"
include "biimpri.mm"
include "sylancr.mm"
include "unblem3.mm"
include "omsmo.mm"
include "syl21anc.mm"

theorem unblem4
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cF: class F
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  assume unblem.2: |- F = ( rec ( ( x e. _V |-> |^| ( A \ suc x ) ) , |^| A ) |` _om )

  disjoint v w
  disjoint v x
  disjoint A v
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint F v
  disjoint F w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F u
  disjoint F y
  disjoint F z
  assert |- ( ( A C_ _om /\ A. w e. _om E. v e. A w e. v ) -> F : _om -1-1-> A )

  proof
    cA
    com
    wss
    #
    vw
    cv
    vv
    cv
    wcel
    vv
    cA
    wrex
    vw
    com
    wral
    #
    wa
    #
    cA
    con0
    wss
    #
    com
    cA
    cF
    wf
    #
    vz
    cv
    #
    cF
    cfv
    #
    @5
    csuc
    cF
    cfv
    wcel
    #
    vz
    com
    wral
    com
    cA
    cF
    wf1
    @0
    @3
    @1
    @0
    com
    con0
    wss
    @3
    omsson
    cA
    com
    con0
    sstr
    mpan2
    adantr
    @2
    cF
    com
    wfn
    #
    @6
    cA
    wcel
    #
    vz
    com
    wral
    #
    @4
    @8
    vx
    cvv
    cA
    vx
    cv
    csuc
    cdif
    cint
    cmpt
    #
    cA
    cint
    #
    crdg
    com
    cres
    #
    com
    wfn
    @12
    @11
    frfnom
    com
    cF
    @13
    unblem.2
    fneq1i
    mpbir
    @2
    @9
    vz
    com
    vx
    vz
    vw
    vv
    cA
    cF
    unblem.2
    unblem2
    ralrimiv
    @4
    @8
    @10
    wa
    vz
    com
    cA
    cF
    ffnfv
    biimpri
    sylancr
    @2
    @7
    vz
    com
    vx
    vz
    vw
    vv
    cA
    cF
    unblem.2
    unblem3
    ralrimiv
    vz
    cA
    cF
    omsmo
    syl21anc
end
