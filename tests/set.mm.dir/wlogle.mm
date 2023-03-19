include "cv.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "wb.mm"
include "3adantr3.mm"
include "mpbid.mm"
include "wloglei.mm"

theorem wlogle
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cS: class S
  assume wlogle.1: |- ( ( z = x /\ w = y ) -> ( ps <-> ch ) )
  assume wlogle.2: |- ( ( z = y /\ w = x ) -> ( ps <-> th ) )
  assume wlogle.3: |- ( ph -> S C_ RR )
  assume wlogle.4: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( ch <-> th ) )
  assume wlogle.5: |- ( ( ph /\ ( x e. S /\ y e. S /\ x <_ y ) ) -> ch )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint ps x
  disjoint ps y
  disjoint ch w
  disjoint ch z
  assert |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ch )

  proof
    wph
    wps
    wch
    wth
    vx
    vy
    vz
    vw
    cS
    wlogle.1
    wlogle.2
    wlogle.3
    wph
    vx
    cv
    #
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    @0
    @2
    cle
    wbr
    #
    w3a
    wa
    wch
    wth
    wlogle.5
    wph
    @1
    @3
    wch
    wth
    wb
    @4
    wlogle.4
    3adantr3
    mpbid
    wlogle.5
    wloglei
end
