include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "3expa.mm"
include "rspcdv.mm"
include "ralrimdva.mm"
include "wrex.mm"
include "r19.29.mm"
include "ad4ant134.mm"
include "exbiri.mm"
include "com23.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "mpan2d.mm"
include "impbid.mm"

theorem ralxfrd2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume ralxfrd2.1: |- ( ( ph /\ y e. C ) -> A e. B )
  assume ralxfrd2.2: |- ( ( ph /\ x e. B ) -> E. y e. C x = A )
  assume ralxfrd2.3: |- ( ( ph /\ y e. C /\ x = A ) -> ( ps <-> ch ) )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint ch x
  disjoint ph x
  disjoint ph y
  disjoint ps y
  assert |- ( ph -> ( A. x e. B ps <-> A. y e. C ch ) )

  proof
    wph
    wps
    vx
    cB
    wral
    #
    wch
    vy
    cC
    wral
    #
    wph
    @0
    wch
    vy
    cC
    wph
    vy
    cv
    cC
    wcel
    #
    wa
    wps
    wch
    vx
    cA
    cB
    ralxfrd2.1
    wph
    @2
    vx
    cv
    #
    cA
    wceq
    #
    wps
    wch
    wb
    #
    ralxfrd2.3
    3expa
    rspcdv
    ralrimdva
    wph
    @1
    wps
    vx
    cB
    wph
    @3
    cB
    wcel
    #
    wa
    #
    @1
    @4
    vy
    cC
    wrex
    #
    wps
    ralxfrd2.2
    @1
    @8
    wa
    wch
    @4
    wa
    #
    vy
    cC
    wrex
    @7
    wps
    wch
    @4
    vy
    cC
    r19.29
    @7
    @9
    wps
    vy
    cC
    @7
    @2
    wa
    #
    wch
    @4
    wps
    @10
    @4
    wch
    wps
    @10
    @4
    wps
    wch
    wph
    @2
    @4
    @5
    @6
    ralxfrd2.3
    ad4ant134
    exbiri
    com23
    impd
    rexlimdva
    syl5
    mpan2d
    ralrimdva
    impbid
end
