include "wfun.mm"
include "cop.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cuz.mm"
include "wfn.mm"
include "uzrdgfni.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "crn.mm"
include "c0.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt2.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "fveq1i.mm"
include "opex.mm"
include "fr0g.mm"
include "eqtri.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "peano1.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "eleqtrri.mm"
include "funopfv.mm"
include "mp2.mm"

theorem uzrdg0i
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let vv: setvar v
  assume om2uz.1: |- C e. ZZ
  assume om2uz.2: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , C ) |` _om )
  assume uzrdg.1: |- A e. _V
  assume uzrdg.2: |- R = ( rec ( ( x e. _V , y e. _V |-> <. ( x + 1 ) , ( x F y ) >. ) , <. C , A >. ) |` _om )
  assume uzrdg.3: |- S = ran R

  disjoint A y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint G y
  disjoint F x
  disjoint F y
  disjoint y z
  disjoint A z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint C w
  disjoint x z
  disjoint C z
  disjoint G v
  disjoint G w
  disjoint G z
  disjoint F w
  disjoint F z
  disjoint R v
  disjoint R w
  disjoint R z
  disjoint S v
  disjoint S w
  disjoint S z
  assert |- ( S ` C ) = A

  proof
    cS
    wfun
    #
    cC
    cA
    cop
    #
    cS
    wcel
    cC
    cS
    cfv
    cA
    wceq
    cS
    cC
    cuz
    cfv
    #
    wfn
    @0
    vx
    vy
    cA
    cC
    cR
    cS
    cF
    cG
    om2uz.1
    om2uz.2
    uzrdg.1
    uzrdg.2
    uzrdg.3
    uzrdgfni
    @2
    cS
    fnfun
    ax-mp
    @1
    cR
    crn
    #
    cS
    c0
    cR
    cfv
    #
    @1
    @3
    @4
    c0
    vx
    vy
    cvv
    cvv
    vx
    cv
    #
    c1
    caddc
    co
    @5
    vy
    cv
    cF
    co
    cop
    cmpt2
    #
    @1
    crdg
    com
    cres
    #
    cfv
    #
    @1
    c0
    cR
    @7
    uzrdg.2
    fveq1i
    @1
    cvv
    wcel
    @8
    @1
    wceq
    cC
    cA
    opex
    @1
    cvv
    @6
    fr0g
    ax-mp
    eqtri
    cR
    com
    wfn
    #
    c0
    com
    wcel
    @4
    @3
    wcel
    @9
    @7
    com
    wfn
    @1
    @6
    frfnom
    com
    cR
    @7
    uzrdg.2
    fneq1i
    mpbir
    peano1
    com
    c0
    cR
    fnfvelrn
    mp2an
    eqeltrri
    uzrdg.3
    eleqtrri
    cC
    cA
    cS
    funopfv
    mp2
end
