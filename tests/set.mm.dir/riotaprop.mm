include "wreu.mm"
include "wcel.mm"
include "crio.mm"
include "riotacl.mm"
include "syl5eqel.mm"
include "wa.mm"
include "wceq.mm"
include "eqcomi.mm"
include "nfriota1.mm"
include "nfcxfr.mm"
include "riota2f.mm"
include "mpbiri.mm"
include "mpancom.mm"
include "jca.mm"

theorem riotaprop
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume riotaprop.0: |- F/ x ps
  assume riotaprop.1: |- B = ( iota_ x e. A ph )
  assume riotaprop.2: |- ( x = B -> ( ph <-> ps ) )

  disjoint A x
  assert |- ( E! x e. A ph -> ( B e. A /\ ps ) )

  proof
    wph
    vx
    cA
    wreu
    #
    cB
    cA
    wcel
    #
    wps
    @0
    cB
    wph
    vx
    cA
    crio
    #
    cA
    riotaprop.1
    wph
    vx
    cA
    riotacl
    syl5eqel
    #
    @1
    @0
    wps
    @3
    @1
    @0
    wa
    wps
    @2
    cB
    wceq
    cB
    @2
    riotaprop.1
    eqcomi
    wph
    wps
    vx
    cA
    cB
    vx
    cB
    @2
    riotaprop.1
    wph
    vx
    cA
    nfriota1
    nfcxfr
    riotaprop.0
    riotaprop.2
    riota2f
    mpbiri
    mpancom
    jca
end
