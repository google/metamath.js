include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "a1i.mm"
include "elmptrab.mm"
include "3simpc.mm"
include "elex.mm"
include "syl.mm"
include "adantr.mm"
include "simpl.mm"
include "simpr.mm"
include "3jca.mm"
include "impbii.mm"
include "bitri.mm"

theorem elmptrab2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cF: class F
  let cW: class W
  let cX: class X
  let cY: class Y
  assume elmptrab2.f: |- F = ( x e. _V |-> { y e. B | ph } )
  assume elmptrab2.s1: |- ( ( x = X /\ y = Y ) -> ( ph <-> ps ) )
  assume elmptrab2.s2: |- ( x = X -> B = C )
  assume elmptrab2.ex: |- B e. _V
  assume elmptrab2.rc: |- ( Y e. C -> X e. W )

  disjoint x y
  disjoint ps x
  disjoint ps y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint C x
  disjoint C y
  disjoint W x
  disjoint W y
  disjoint B y
  assert |- ( Y e. ( F ` X ) <-> ( Y e. C /\ ps ) )

  proof
    cY
    cX
    cF
    cfv
    wcel
    cX
    cvv
    wcel
    #
    cY
    cC
    wcel
    #
    wps
    w3a
    #
    @1
    wps
    wa
    #
    wph
    wps
    vx
    vy
    cB
    cC
    cvv
    cF
    cvv
    cX
    cY
    elmptrab2.f
    elmptrab2.s1
    elmptrab2.s2
    cB
    cvv
    wcel
    vx
    cv
    cvv
    wcel
    elmptrab2.ex
    a1i
    elmptrab
    @2
    @3
    @0
    @1
    wps
    3simpc
    @3
    @0
    @1
    wps
    @1
    @0
    wps
    @1
    cX
    cW
    wcel
    @0
    elmptrab2.rc
    cX
    cW
    elex
    syl
    adantr
    @1
    wps
    simpl
    @1
    wps
    simpr
    3jca
    impbii
    bitri
end
