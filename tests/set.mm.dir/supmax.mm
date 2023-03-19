include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "simprr.mm"
include "breq2.mm"
include "rspcev.mm"
include "syl2an2r.mm"
include "eqsupd.mm"

theorem supmax
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vz: setvar z
  assume supmax.1: |- ( ph -> R Or A )
  assume supmax.2: |- ( ph -> C e. A )
  assume supmax.3: |- ( ph -> C e. B )
  assume supmax.4: |- ( ( ph /\ y e. B ) -> -. C R y )

  disjoint A y
  disjoint B y
  disjoint C y
  disjoint R y
  disjoint ph y
  disjoint A z
  disjoint y z
  disjoint B z
  disjoint C z
  disjoint R z
  assert |- ( ph -> sup ( B , A , R ) = C )

  proof
    wph
    vy
    vz
    cA
    cB
    cC
    cR
    supmax.1
    supmax.2
    supmax.4
    wph
    cC
    cB
    wcel
    vy
    cv
    #
    cA
    wcel
    #
    @0
    cC
    cR
    wbr
    #
    wa
    @2
    @0
    vz
    cv
    #
    cR
    wbr
    #
    vz
    cB
    wrex
    supmax.3
    wph
    @1
    @2
    simprr
    @4
    @2
    vz
    cC
    cB
    @3
    cC
    @0
    cR
    breq2
    rspcev
    syl2an2r
    eqsupd
end
