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
include "zprodn0.mm"

theorem iprodn0
  let wph: wff ph
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  assume zprodn0.1: |- Z = ( ZZ>= ` M )
  assume zprodn0.2: |- ( ph -> M e. ZZ )
  assume zprodn0.3: |- ( ph -> X =/= 0 )
  assume zprodn0.4: |- ( ph -> seq M ( x. , F ) ~~> X )
  assume iprodn0.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume iprodn0.6: |- ( ( ph /\ k e. Z ) -> B e. CC )

  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint Z k
  assert |- ( ph -> prod_ k e. Z B = X )

  proof
    wph
    cZ
    cB
    vk
    cF
    cM
    cX
    cZ
    zprodn0.1
    zprodn0.2
    zprodn0.3
    zprodn0.4
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
    iprodn0.5
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
    iprodn0.6
    zprodn0
end
