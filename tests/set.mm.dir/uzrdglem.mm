include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "ccnv.mm"
include "c2nd.mm"
include "cop.mm"
include "crn.mm"
include "com.mm"
include "wceq.mm"
include "wf1o.mm"
include "om2uzf1oi.mm"
include "f1ocnvdm.mm"
include "mpan.mm"
include "om2uzrdg.mm"
include "syl.mm"
include "f1ocnvfv2.mm"
include "opeq1d.mm"
include "eqtrd.mm"
include "wfn.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt2.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "eqeltrrd.mm"

theorem uzrdglem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume om2uz.1: |- C e. ZZ
  assume om2uz.2: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , C ) |` _om )
  assume uzrdg.1: |- A e. _V
  assume uzrdg.2: |- R = ( rec ( ( x e. _V , y e. _V |-> <. ( x + 1 ) , ( x F y ) >. ) , <. C , A >. ) |` _om )

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
  assert |- ( B e. ( ZZ>= ` C ) -> <. B , ( 2nd ` ( R ` ( `' G ` B ) ) ) >. e. ran R )

  proof
    cB
    cC
    cuz
    cfv
    #
    wcel
    #
    cB
    cG
    ccnv
    cfv
    #
    cR
    cfv
    #
    cB
    @3
    c2nd
    cfv
    #
    cop
    #
    cR
    crn
    #
    @1
    @3
    @2
    cG
    cfv
    #
    @4
    cop
    #
    @5
    @1
    @2
    com
    wcel
    #
    @3
    @8
    wceq
    com
    @0
    cG
    wf1o
    #
    @1
    @9
    vx
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzf1oi
    #
    com
    @0
    cB
    cG
    f1ocnvdm
    mpan
    #
    vx
    vy
    cA
    @2
    cC
    cR
    cF
    cG
    om2uz.1
    om2uz.2
    uzrdg.1
    uzrdg.2
    om2uzrdg
    syl
    @1
    @7
    cB
    @4
    @10
    @1
    @7
    cB
    wceq
    @11
    com
    @0
    cB
    cG
    f1ocnvfv2
    mpan
    opeq1d
    eqtrd
    @1
    cR
    com
    wfn
    #
    @9
    @3
    @6
    wcel
    @13
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
    @14
    vy
    cv
    cF
    co
    cop
    cmpt2
    #
    cC
    cA
    cop
    #
    crdg
    com
    cres
    #
    com
    wfn
    @16
    @15
    frfnom
    com
    cR
    @17
    uzrdg.2
    fneq1i
    mpbir
    @12
    com
    @2
    cR
    fnfvelrn
    sylancr
    eqeltrrd
end
