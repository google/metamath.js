include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "pm5.74da.mm"
include "albid.mm"
include "df-ral.mm"
include "3bitr4g.mm"

theorem ralbida
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume ralbida.1: |- F/ x ph
  assume ralbida.2: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )


  assert |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    wps
    wi
    #
    vx
    wal
    @0
    wch
    wi
    #
    vx
    wal
    wps
    vx
    cA
    wral
    wch
    vx
    cA
    wral
    wph
    @1
    @2
    vx
    ralbida.1
    wph
    @0
    wps
    wch
    ralbida.2
    pm5.74da
    albid
    wps
    vx
    cA
    df-ral
    wch
    vx
    cA
    df-ral
    3bitr4g
end
