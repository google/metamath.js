include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "com.mm"
include "suceq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "wcel.mm"
include "cvv.mm"
include "ovex.mm"
include "oveq1.mm"
include "frsucmpt2.mm"
include "mpan2.mm"
include "vtoclga.mm"

theorem om2uzsuci
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let vv: setvar v
  assume om2uz.1: |- C e. ZZ
  assume om2uz.2: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , C ) |` _om )

  disjoint C x
  disjoint y z
  disjoint A y
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
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint G z
  assert |- ( A e. _om -> ( G ` suc A ) = ( ( G ` A ) + 1 ) )

  proof
    vz
    cv
    #
    csuc
    #
    cG
    cfv
    #
    @0
    cG
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    #
    cA
    csuc
    #
    cG
    cfv
    #
    cA
    cG
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    vz
    cA
    com
    @0
    cA
    wceq
    #
    @2
    @7
    @4
    @9
    @10
    @1
    @6
    cG
    @0
    cA
    suceq
    fveq2d
    @10
    @3
    @8
    c1
    caddc
    @0
    cA
    cG
    fveq2
    oveq1d
    eqeq12d
    @0
    com
    wcel
    @4
    cvv
    wcel
    @5
    @3
    c1
    caddc
    ovex
    vx
    vy
    cC
    @0
    vx
    cv
    #
    c1
    caddc
    co
    @4
    vy
    cv
    #
    c1
    caddc
    co
    cG
    cvv
    om2uz.2
    @12
    @11
    c1
    caddc
    oveq1
    @12
    @3
    c1
    caddc
    oveq1
    frsucmpt2
    mpan2
    vtoclga
end
