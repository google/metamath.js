include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "cio.mm"
include "alrimiv.mm"
include "wi.mm"
include "eqeq2.mm"
include "bibi2d.mm"
include "albidv.mm"
include "imbi12d.mm"
include "iotaval.mm"
include "vtoclg.mm"
include "adantl.mm"
include "mpd.mm"

theorem iota5
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  assume iota5.1: |- ( ( ph /\ A e. V ) -> ( ps <-> x = A ) )

  disjoint A x
  disjoint V x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint ps y
  assert |- ( ( ph /\ A e. V ) -> ( iota x ps ) = A )

  proof
    wph
    cA
    cV
    wcel
    #
    wa
    #
    wps
    vx
    cv
    #
    cA
    wceq
    #
    wb
    #
    vx
    wal
    #
    wps
    vx
    cio
    #
    cA
    wceq
    #
    @1
    @4
    vx
    iota5.1
    alrimiv
    @0
    @5
    @7
    wi
    #
    wph
    wps
    @2
    vy
    cv
    #
    wceq
    #
    wb
    #
    vx
    wal
    #
    @6
    @9
    wceq
    #
    wi
    @8
    vy
    cA
    cV
    @9
    cA
    wceq
    #
    @12
    @5
    @13
    @7
    @14
    @11
    @4
    vx
    @14
    @10
    @3
    wps
    @9
    cA
    @2
    eqeq2
    bibi2d
    albidv
    @9
    cA
    @6
    eqeq2
    imbi12d
    wps
    vx
    vy
    iotaval
    vtoclg
    adantl
    mpd
end
