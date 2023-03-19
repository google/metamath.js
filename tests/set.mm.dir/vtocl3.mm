include "wal.mm"
include "wi.mm"
include "wex.mm"
include "cv.mm"
include "wceq.mm"
include "isseti.mm"
include "w3a.mm"
include "eeeanv.mm"
include "biimpd.mm"
include "eximi.mm"
include "2eximi.mm"
include "sylbir.mm"
include "mp3an.mm"
include "19.36v.mm"
include "2exbii.mm"
include "mpbi.mm"
include "exbii.mm"
include "19.36iv.mm"
include "gen2.mm"
include "mpg.mm"

theorem vtocl3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  assume vtocl3.1: |- A e. _V
  assume vtocl3.2: |- B e. _V
  assume vtocl3.3: |- C e. _V
  assume vtocl3.4: |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) )
  assume vtocl3.5: |- ph

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ps x
  disjoint ps y
  disjoint ps z
  assert |- ps

  proof
    wph
    vz
    wal
    #
    vy
    wal
    #
    wps
    vx
    @1
    wps
    vx
    @0
    wps
    wi
    #
    vy
    wex
    #
    vx
    wex
    #
    @1
    wps
    wi
    #
    vx
    wex
    wph
    wps
    wi
    #
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    @4
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
    vz
    cv
    cC
    wceq
    #
    vz
    wex
    #
    @8
    vx
    cA
    vtocl3.1
    isseti
    vy
    cB
    vtocl3.2
    isseti
    vz
    cC
    vtocl3.3
    isseti
    @10
    @12
    @14
    w3a
    @9
    @11
    @13
    w3a
    #
    vz
    wex
    #
    vy
    wex
    vx
    wex
    @8
    @9
    @11
    @13
    vx
    vy
    vz
    eeeanv
    @16
    @7
    vx
    vy
    @15
    @6
    vz
    @15
    wph
    wps
    vtocl3.4
    biimpd
    eximi
    2eximi
    sylbir
    mp3an
    @7
    @2
    vx
    vy
    wph
    wps
    vz
    19.36v
    2exbii
    mpbi
    @3
    @5
    vx
    @0
    wps
    vy
    19.36v
    exbii
    mpbi
    19.36iv
    wph
    vy
    vz
    vtocl3.5
    gen2
    mpg
end
