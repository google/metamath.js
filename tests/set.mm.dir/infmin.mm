include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "adantr.mm"
include "simprr.mm"
include "breq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eqinfd.mm"

theorem infmin
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vz: setvar z
  assume infmin.1: |- ( ph -> R Or A )
  assume infmin.2: |- ( ph -> C e. A )
  assume infmin.3: |- ( ph -> C e. B )
  assume infmin.4: |- ( ( ph /\ y e. B ) -> -. y R C )

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
  disjoint ph z
  assert |- ( ph -> inf ( B , A , R ) = C )

  proof
    wph
    vy
    vz
    cA
    cB
    cC
    cR
    infmin.1
    infmin.2
    infmin.4
    wph
    vy
    cv
    #
    cA
    wcel
    #
    cC
    @0
    cR
    wbr
    #
    wa
    #
    wa
    cC
    cB
    wcel
    #
    @2
    vz
    cv
    #
    @0
    cR
    wbr
    #
    vz
    cB
    wrex
    wph
    @4
    @3
    infmin.3
    adantr
    wph
    @1
    @2
    simprr
    @6
    @2
    vz
    cC
    cB
    @5
    cC
    @0
    cR
    breq1
    rspcev
    syl2anc
    eqinfd
end
