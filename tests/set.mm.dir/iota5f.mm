include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "cio.mm"
include "nfel1.mm"
include "nfan.mm"
include "alrimi.mm"
include "wi.mm"
include "weq.mm"
include "nfeq2.mm"
include "eqeq2.mm"
include "bibi2d.mm"
include "albid.mm"
include "imbi12d.mm"
include "iotaval.mm"
include "vtoclg.mm"
include "adantl.mm"
include "mpd.mm"

theorem iota5f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  assume iota5f.1: |- F/ x ph
  assume iota5f.2: |- F/_ x A
  assume iota5f.3: |- ( ( ph /\ A e. V ) -> ( ps <-> x = A ) )

  disjoint V x
  disjoint A y
  disjoint ps y
  disjoint x y
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
    wph
    @0
    vx
    iota5f.1
    vx
    cA
    cV
    iota5f.2
    nfel1
    nfan
    iota5f.3
    alrimi
    @0
    @5
    @7
    wi
    #
    wph
    wps
    vx
    vy
    weq
    #
    wb
    #
    vx
    wal
    #
    @6
    vy
    cv
    #
    wceq
    #
    wi
    @8
    vy
    cA
    cV
    @12
    cA
    wceq
    #
    @11
    @5
    @13
    @7
    @14
    @10
    @4
    vx
    vx
    @12
    cA
    iota5f.2
    nfeq2
    @14
    @9
    @3
    wps
    @12
    cA
    @2
    eqeq2
    bibi2d
    albid
    @12
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
