include "wal.mm"
include "wi.mm"
include "wex.mm"
include "cv.mm"
include "wceq.mm"
include "isseti.mm"
include "wa.mm"
include "eeanv.mm"
include "biimpd.mm"
include "2eximi.mm"
include "sylbir.mm"
include "mp2an.mm"
include "19.36v.mm"
include "exbii.mm"
include "mpbi.mm"
include "19.36iv.mm"
include "ax-gen.mm"
include "mpg.mm"

theorem vtocl2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume vtocl2.1: |- A e. _V
  assume vtocl2.2: |- B e. _V
  assume vtocl2.3: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )
  assume vtocl2.4: |- ph

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ps x
  disjoint ps y
  assert |- ps

  proof
    wph
    vy
    wal
    #
    wps
    vx
    @0
    wps
    vx
    wph
    wps
    wi
    #
    vy
    wex
    #
    vx
    wex
    #
    @0
    wps
    wi
    #
    vx
    wex
    vx
    cv
    cA
    wceq
    #
    vx
    wex
    #
    vy
    cv
    cB
    wceq
    #
    vy
    wex
    #
    @3
    vx
    cA
    vtocl2.1
    isseti
    vy
    cB
    vtocl2.2
    isseti
    @6
    @8
    wa
    @5
    @7
    wa
    #
    vy
    wex
    vx
    wex
    @3
    @5
    @7
    vx
    vy
    eeanv
    @9
    @1
    vx
    vy
    @9
    wph
    wps
    vtocl2.3
    biimpd
    2eximi
    sylbir
    mp2an
    @2
    @4
    vx
    wph
    wps
    vy
    19.36v
    exbii
    mpbi
    19.36iv
    wph
    vy
    vtocl2.4
    ax-gen
    mpg
end
