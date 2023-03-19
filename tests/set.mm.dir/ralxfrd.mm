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
include "wi.mm"
include "r19.29.mm"
include "exbiri.mm"
include "com23.mm"
include "impd.mm"
include "rexlimdvw.mm"
include "syl5.mm"
include "adantr.mm"
include "mpan2d.mm"
include "impbid.mm"

theorem ralxfrd
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
    @1
    @4
    vy
    cC
    wrex
    #
    wps
    ralxfrd.2
    wph
    @1
    @6
    wa
    #
    wps
    wi
    @5
    @7
    wch
    @4
    wa
    #
    vy
    cC
    wrex
    wph
    wps
    wch
    @4
    vy
    cC
    r19.29
    wph
    @8
    wps
    vy
    cC
    wph
    wch
    @4
    wps
    wph
    @4
    wch
    wps
    wph
    @4
    wps
    wch
    ralxfrd.3
    exbiri
    com23
    impd
    rexlimdvw
    syl5
    adantr
    mpan2d
    ralrimdva
    impbid
end
