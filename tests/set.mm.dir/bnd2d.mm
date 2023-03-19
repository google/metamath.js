include "cvv.mm"
include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "c0.mm"
include "cif.mm"
include "wceq.mm"
include "raleq.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "0ex.mm"
include "elimel.mm"
include "bnd2.mm"
include "dedth.mm"
include "sylc.mm"

theorem bnd2d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume bnd2d.1: |- ( ph -> A e. _V )
  assume bnd2d.2: |- ( ph -> A. x e. A E. y e. B ps )

  disjoint ps z
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint y z
  disjoint B z
  disjoint k x
  assert |- ( ph -> E. z ( z C_ B /\ A. x e. A E. y e. z ps ) )

  proof
    wph
    cA
    cvv
    wcel
    #
    wps
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    vz
    cv
    #
    cB
    wss
    #
    wps
    vy
    @3
    wrex
    #
    vx
    cA
    wral
    #
    wa
    #
    vz
    wex
    #
    bnd2d.1
    bnd2d.2
    @0
    @2
    @8
    wi
    @1
    vx
    @0
    cA
    c0
    cif
    #
    wral
    #
    @4
    @5
    vx
    @9
    wral
    #
    wa
    #
    vz
    wex
    #
    wi
    cA
    c0
    cA
    @9
    wceq
    #
    @2
    @10
    @8
    @13
    @1
    vx
    cA
    @9
    raleq
    @14
    @7
    @12
    vz
    @14
    @6
    @11
    @4
    @5
    vx
    cA
    @9
    raleq
    anbi2d
    exbidv
    imbi12d
    wps
    vx
    vy
    vz
    @9
    cB
    cA
    c0
    cvv
    0ex
    elimel
    bnd2
    dedth
    sylc
end
