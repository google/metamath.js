include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wrex.mm"
include "simpl1.mm"
include "simpl2.mm"
include "rspcev.mm"
include "3ad2antl3.mm"
include "cv.mm"
include "wceq.mm"
include "rexbidv.mm"
include "rspc2ev.mm"
include "syl3anc.mm"

theorem rspc3ev
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  assume rspc3v.1: |- ( x = A -> ( ph <-> ch ) )
  assume rspc3v.2: |- ( y = B -> ( ch <-> th ) )
  assume rspc3v.3: |- ( z = C -> ( th <-> ps ) )

  disjoint ps z
  disjoint ch x
  disjoint th y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint R x
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( ( A e. R /\ B e. S /\ C e. T ) /\ ps ) -> E. x e. R E. y e. S E. z e. T ph )

  proof
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cT
    wcel
    #
    w3a
    wps
    wa
    @0
    @1
    wth
    vz
    cT
    wrex
    #
    wph
    vz
    cT
    wrex
    #
    vy
    cS
    wrex
    vx
    cR
    wrex
    @0
    @1
    @2
    wps
    simpl1
    @0
    @1
    @2
    wps
    simpl2
    @2
    @0
    wps
    @3
    @1
    wth
    wps
    vz
    cC
    cT
    rspc3v.3
    rspcev
    3ad2antl3
    @4
    @3
    wch
    vz
    cT
    wrex
    vx
    vy
    cA
    cB
    cR
    cS
    vx
    cv
    cA
    wceq
    wph
    wch
    vz
    cT
    rspc3v.1
    rexbidv
    vy
    cv
    cB
    wceq
    wch
    wth
    vz
    cT
    rspc3v.2
    rexbidv
    rspc2ev
    syl3anc
end
