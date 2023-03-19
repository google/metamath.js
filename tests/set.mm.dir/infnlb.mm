include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "cinf.mm"
include "wa.mm"
include "wrex.mm"
include "infglb.mm"
include "expdimp.mm"
include "dfrex2.mm"
include "syl6ib.mm"
include "con2d.mm"
include "expimpd.mm"

theorem infnlb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume infcl.1: |- ( ph -> R Or A )
  assume infcl.2: |- ( ph -> E. x e. A ( A. y e. B -. y R x /\ A. y e. A ( x R y -> E. z e. B z R y ) ) )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint C z
  disjoint ph z
  assert |- ( ph -> ( ( C e. A /\ A. z e. B -. z R C ) -> -. inf ( B , A , R ) R C ) )

  proof
    wph
    cC
    cA
    wcel
    #
    vz
    cv
    cC
    cR
    wbr
    #
    wn
    vz
    cB
    wral
    #
    cB
    cA
    cR
    cinf
    cC
    cR
    wbr
    #
    wn
    wph
    @0
    wa
    #
    @3
    @2
    @4
    @3
    @1
    vz
    cB
    wrex
    #
    @2
    wn
    wph
    @0
    @3
    @5
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cR
    infcl.1
    infcl.2
    infglb
    expdimp
    @1
    vz
    cB
    dfrex2
    syl6ib
    con2d
    expimpd
end
