include "cv.mm"
include "cin.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "elinel1.mm"
include "imim1i.mm"
include "ralimi2.mm"
include "imim12i.mm"
include "syl.mm"
include "elinel2.mm"
include "r19.26-2.mm"
include "sylanbrc.mm"
include "elin.mm"
include "2ralbii.mm"
include "sylibr.mm"
include "eleq2d.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "raleqdv.mm"

theorem fiinfi
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume fiinfi.a: |- ( ph -> A. x e. A A. y e. A ( x i^i y ) e. A )
  assume fiinfi.b: |- ( ph -> A. x e. B A. y e. B ( x i^i y ) e. B )
  assume fiinfi.c: |- ( ph -> C = ( A i^i B ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A. x e. C A. y e. C ( x i^i y ) e. C )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    cC
    wcel
    #
    vy
    cC
    wral
    #
    vx
    cC
    wral
    @4
    vx
    cA
    cB
    cin
    #
    wral
    #
    wph
    @6
    @3
    vy
    @5
    wral
    #
    vx
    @5
    wral
    #
    wph
    @8
    @2
    @5
    wcel
    #
    vy
    @5
    wral
    #
    vx
    @5
    wral
    #
    wph
    @2
    cA
    wcel
    #
    @2
    cB
    wcel
    #
    wa
    #
    vy
    @5
    wral
    vx
    @5
    wral
    #
    @11
    wph
    @12
    vy
    @5
    wral
    #
    vx
    @5
    wral
    #
    @13
    vy
    @5
    wral
    #
    vx
    @5
    wral
    #
    @15
    wph
    @12
    vy
    cA
    wral
    #
    vx
    cA
    wral
    @17
    fiinfi.a
    @20
    @16
    vx
    cA
    @5
    @0
    @5
    wcel
    #
    @0
    cA
    wcel
    @20
    @16
    @0
    cA
    cB
    elinel1
    @12
    @12
    vy
    cA
    @5
    @1
    @5
    wcel
    #
    @1
    cA
    wcel
    @12
    @1
    cA
    cB
    elinel1
    imim1i
    ralimi2
    imim12i
    ralimi2
    syl
    wph
    @13
    vy
    cB
    wral
    #
    vx
    cB
    wral
    @19
    fiinfi.b
    @23
    @18
    vx
    cB
    @5
    @21
    @0
    cB
    wcel
    @23
    @18
    @0
    cA
    cB
    elinel2
    @13
    @13
    vy
    cB
    @5
    @22
    @1
    cB
    wcel
    @13
    @1
    cA
    cB
    elinel2
    imim1i
    ralimi2
    imim12i
    ralimi2
    syl
    @12
    @13
    vx
    vy
    @5
    @5
    r19.26-2
    sylanbrc
    @9
    @14
    vx
    vy
    @5
    @5
    @2
    cA
    cB
    elin
    2ralbii
    sylibr
    wph
    @7
    @10
    vx
    @5
    wph
    @3
    @9
    vy
    @5
    wph
    cC
    @5
    @2
    fiinfi.c
    eleq2d
    ralbidv
    ralbidv
    mpbird
    wph
    @4
    @7
    vx
    @5
    wph
    @3
    vy
    cC
    @5
    fiinfi.c
    raleqdv
    ralbidv
    mpbird
    wph
    @4
    vx
    cC
    @5
    fiinfi.c
    raleqdv
    mpbird
end
