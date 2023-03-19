include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wcel.mm"
include "df-ral.mm"
include "imbi1d.mm"
include "albidv.mm"
include "syl5bb.mm"
include "ralcom4.mm"
include "ralbii.mm"
include "r19.23v.mm"
include "bitr2i.mm"
include "albii.mm"
include "3bitr4ri.mm"
include "syl6bb.mm"
include "pm5.74da.mm"
include "biidd.mm"
include "ceqsalv.mm"
include "2ralbidv.mm"
include "bitrd.mm"

theorem ralxpxfr2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ralxpxfr2d.a: |- A e. _V
  assume ralxpxfr2d.b: |- ( ph -> ( x e. B <-> E. y e. C E. z e. D x = A ) )
  assume ralxpxfr2d.c: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )

  disjoint ph x
  disjoint ph z
  disjoint x z
  disjoint ph y
  disjoint x y
  disjoint ps y
  disjoint ps z
  disjoint A x
  disjoint C x
  disjoint D x
  disjoint ch x
  assert |- ( ph -> ( A. x e. B ps <-> A. y e. C A. z e. D ch ) )

  proof
    wph
    wps
    vx
    cB
    wral
    #
    vx
    cv
    #
    cA
    wceq
    #
    wps
    wi
    #
    vx
    wal
    #
    vz
    cD
    wral
    #
    vy
    cC
    wral
    #
    wch
    vz
    cD
    wral
    vy
    cC
    wral
    wph
    @0
    @2
    vz
    cD
    wrex
    #
    vy
    cC
    wrex
    #
    wps
    wi
    #
    vx
    wal
    #
    @6
    @0
    @1
    cB
    wcel
    #
    wps
    wi
    #
    vx
    wal
    wph
    @10
    wps
    vx
    cB
    df-ral
    wph
    @12
    @9
    vx
    wph
    @11
    @8
    wps
    ralxpxfr2d.b
    imbi1d
    albidv
    syl5bb
    @3
    vz
    cD
    wral
    #
    vx
    wal
    #
    vy
    cC
    wral
    @13
    vy
    cC
    wral
    #
    vx
    wal
    @6
    @10
    @13
    vy
    vx
    cC
    ralcom4
    @5
    @14
    vy
    cC
    @3
    vz
    vx
    cD
    ralcom4
    ralbii
    @9
    @15
    vx
    @15
    @7
    wps
    wi
    #
    vy
    cC
    wral
    @9
    @13
    @16
    vy
    cC
    @2
    wps
    vz
    cD
    r19.23v
    ralbii
    @7
    wps
    vy
    cC
    r19.23v
    bitr2i
    albii
    3bitr4ri
    syl6bb
    wph
    @4
    wch
    vy
    vz
    cC
    cD
    wph
    @4
    @2
    wch
    wi
    #
    vx
    wal
    wch
    wph
    @3
    @17
    vx
    wph
    @2
    wps
    wch
    ralxpxfr2d.c
    pm5.74da
    albidv
    wch
    wch
    vx
    cA
    ralxpxfr2d.a
    @2
    wch
    biidd
    ceqsalv
    syl6bb
    2ralbidv
    bitrd
end
