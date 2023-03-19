include "cinf.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "infcl.mm"
include "sseld.mm"
include "inflb.mm"
include "syld.mm"
include "ralrimiv.mm"
include "infnlb.mm"
include "mp2and.mm"

theorem infssd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume infssd.0: |- ( ph -> R Or A )
  assume infssd.1: |- ( ph -> C C_ B )
  assume infssd.3: |- ( ph -> E. x e. A ( A. y e. C -. y R x /\ A. y e. A ( x R y -> E. z e. C z R y ) ) )
  assume infssd.4: |- ( ph -> E. x e. A ( A. y e. B -. y R x /\ A. y e. A ( x R y -> E. z e. B z R y ) ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint ph z
  assert |- ( ph -> -. inf ( C , A , R ) R inf ( B , A , R ) )

  proof
    wph
    cB
    cA
    cR
    cinf
    #
    cA
    wcel
    vz
    cv
    #
    @0
    cR
    wbr
    wn
    #
    vz
    cC
    wral
    cC
    cA
    cR
    cinf
    @0
    cR
    wbr
    wn
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    infssd.0
    infssd.4
    infcl
    wph
    @2
    vz
    cC
    wph
    @1
    cC
    wcel
    @1
    cB
    wcel
    @2
    wph
    cC
    cB
    @1
    infssd.1
    sseld
    wph
    vx
    vy
    vz
    cA
    cB
    @1
    cR
    infssd.0
    infssd.4
    inflb
    syld
    ralrimiv
    wph
    vx
    vy
    vz
    cA
    cC
    @0
    cR
    infssd.0
    infssd.3
    infnlb
    mp2and
end
