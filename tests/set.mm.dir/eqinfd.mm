include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cinf.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "expr.mm"
include "eqinf.mm"
include "mp3and.mm"

theorem eqinfd
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume infexd.1: |- ( ph -> R Or A )
  assume eqinfd.2: |- ( ph -> C e. A )
  assume eqinfd.3: |- ( ( ph /\ y e. B ) -> -. y R C )
  assume eqinfd.4: |- ( ( ph /\ ( y e. A /\ C R y ) ) -> E. z e. B z R y )

  disjoint C y
  disjoint C z
  disjoint y z
  disjoint ph y
  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint R y
  disjoint R z
  assert |- ( ph -> inf ( B , A , R ) = C )

  proof
    wph
    cC
    cA
    wcel
    vy
    cv
    #
    cC
    cR
    wbr
    wn
    #
    vy
    cB
    wral
    cC
    @0
    cR
    wbr
    #
    vz
    cv
    @0
    cR
    wbr
    vz
    cB
    wrex
    #
    wi
    #
    vy
    cA
    wral
    cB
    cA
    cR
    cinf
    cC
    wceq
    eqinfd.2
    wph
    @1
    vy
    cB
    eqinfd.3
    ralrimiva
    wph
    @4
    vy
    cA
    wph
    @0
    cA
    wcel
    @2
    @3
    eqinfd.4
    expr
    ralrimiva
    wph
    vy
    vz
    cA
    cB
    cC
    cR
    infexd.1
    eqinf
    mp3and
end
