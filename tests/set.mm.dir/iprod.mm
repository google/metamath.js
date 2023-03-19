include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "zprod.mm"

theorem iprod
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume zprod.1: |- Z = ( ZZ>= ` M )
  assume zprod.2: |- ( ph -> M e. ZZ )
  assume zprod.3: |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) )
  assume iprod.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume iprod.5: |- ( ( ph /\ k e. Z ) -> B e. CC )

  disjoint B n
  disjoint B y
  disjoint F k
  disjoint k n
  disjoint k ph
  disjoint k y
  disjoint M k
  disjoint M y
  disjoint n ph
  disjoint n y
  disjoint ph y
  disjoint Z k
  disjoint Z n
  disjoint Z y
  assert |- ( ph -> prod_ k e. Z B = ( ~~> ` seq M ( x. , F ) ) )

  proof
    wph
    vy
    cZ
    cB
    vk
    vn
    cF
    cM
    cZ
    zprod.1
    zprod.2
    zprod.3
    cZ
    cZ
    wss
    wph
    cZ
    ssid
    a1i
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    @0
    cF
    cfv
    cB
    @1
    cB
    c1
    cif
    #
    iprod.4
    @1
    @2
    cB
    wceq
    wph
    @1
    cB
    c1
    iftrue
    adantl
    eqtr4d
    iprod.5
    zprod
end
