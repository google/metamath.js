include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "zsum.mm"

theorem isum
  let wph: wff ph
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  assume zsum.1: |- Z = ( ZZ>= ` M )
  assume zsum.2: |- ( ph -> M e. ZZ )
  assume isum.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume isum.4: |- ( ( ph /\ k e. Z ) -> B e. CC )

  disjoint F k
  disjoint k ph
  disjoint Z k
  disjoint M k
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint A f
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint A g
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint A i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint A j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint F j
  disjoint F n
  disjoint F x
  disjoint f ph
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint m ph
  disjoint ph x
  disjoint B f
  disjoint B g
  disjoint B i
  disjoint B j
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint M f
  disjoint M g
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint M x
  assert |- ( ph -> sum_ k e. Z B = ( ~~> ` seq M ( + , F ) ) )

  proof
    wph
    cZ
    cB
    vk
    cF
    cM
    cZ
    zsum.1
    zsum.2
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
    cc0
    cif
    #
    isum.3
    @1
    @2
    cB
    wceq
    wph
    @1
    cB
    cc0
    iftrue
    adantl
    eqtr4d
    isum.4
    zsum
end
