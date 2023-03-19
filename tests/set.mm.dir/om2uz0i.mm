include "c0.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "fveq1i.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem om2uz0i
  let vx: setvar x
  let cC: class C
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  let cA: class A
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
  assert |- ( G ` (/) ) = C

  proof
    c0
    cG
    cfv
    c0
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    #
    cC
    crdg
    com
    cres
    #
    cfv
    #
    cC
    c0
    cG
    @1
    om2uz.2
    fveq1i
    cC
    cz
    wcel
    @2
    cC
    wceq
    om2uz.1
    cC
    cz
    @0
    fr0g
    ax-mp
    eqtri
end
