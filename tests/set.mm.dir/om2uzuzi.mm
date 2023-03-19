include "cv.mm"
include "cfv.mm"
include "cuz.mm"
include "wcel.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "om2uz0i.mm"
include "cz.mm"
include "uzid.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "com.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "peano2uz.mm"
include "om2uzsuci.mm"
include "syl5ibr.mm"
include "finds.mm"

theorem om2uzuzi
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
  assert |- ( A e. _om -> ( G ` A ) e. ( ZZ>= ` C ) )

  proof
    vy
    cv
    #
    cG
    cfv
    #
    cC
    cuz
    cfv
    #
    wcel
    c0
    cG
    cfv
    #
    @2
    wcel
    vz
    cv
    #
    cG
    cfv
    #
    @2
    wcel
    #
    @4
    csuc
    #
    cG
    cfv
    #
    @2
    wcel
    #
    cA
    cG
    cfv
    #
    @2
    wcel
    vy
    vz
    cA
    @0
    c0
    wceq
    @1
    @3
    @2
    @0
    c0
    cG
    fveq2
    eleq1d
    @0
    @4
    wceq
    @1
    @5
    @2
    @0
    @4
    cG
    fveq2
    eleq1d
    @0
    @7
    wceq
    @1
    @8
    @2
    @0
    @7
    cG
    fveq2
    eleq1d
    @0
    cA
    wceq
    @1
    @10
    @2
    @0
    cA
    cG
    fveq2
    eleq1d
    @3
    cC
    @2
    vx
    cC
    cG
    om2uz.1
    om2uz.2
    om2uz0i
    cC
    cz
    wcel
    cC
    @2
    wcel
    om2uz.1
    cC
    uzid
    ax-mp
    eqeltri
    @6
    @9
    @4
    com
    wcel
    #
    @5
    c1
    caddc
    co
    #
    @2
    wcel
    cC
    @5
    peano2uz
    @11
    @8
    @12
    @2
    vx
    @4
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzsuci
    eleq1d
    syl5ibr
    finds
end
