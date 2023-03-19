include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "adantlr.mm"
include "rspcdv.mm"
include "ralrimdva.mm"
include "wrex.mm"
include "r19.29.mm"
include "wi.mm"
include "biimprd.mm"
include "expimpd.mm"
include "ancomsd.mm"
include "ad2antrr.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "mpan2d.mm"
include "impbid.mm"

theorem ralxfrdOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume ralxfrd.1: |- ( ( ph /\ y e. C ) -> A e. B )
  assume ralxfrd.2: |- ( ( ph /\ x e. B ) -> E. y e. C x = A )
  assume ralxfrd.3: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )

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
    ralxfrd.1
    wph
    vx
    cv
    #
    cA
    wceq
    #
    wps
    wch
    wb
    @2
    ralxfrd.3
    adantlr
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
    ralxfrd.2
    @1
    @7
    wa
    wch
    @4
    wa
    #
    vy
    cC
    wrex
    @6
    wps
    wch
    @4
    vy
    cC
    r19.29
    @6
    @8
    wps
    vy
    cC
    wph
    @8
    wps
    wi
    @5
    @2
    wph
    @4
    wch
    wps
    wph
    @4
    wch
    wps
    wph
    @4
    wa
    wps
    wch
    ralxfrd.3
    biimprd
    expimpd
    ancomsd
    ad2antrr
    rexlimdva
    syl5
    mpan2d
    ralrimdva
    impbid
end
