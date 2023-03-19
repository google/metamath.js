include "cv.mm"
include "com.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "eqid.mm"
include "a1i.mm"
include "wi.mm"
include "a1d.mm"
include "finds2.mm"
include "mpi.mm"

theorem finds1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  assume finds1.1: |- ( x = (/) -> ( ph <-> ps ) )
  assume finds1.2: |- ( x = y -> ( ph <-> ch ) )
  assume finds1.3: |- ( x = suc y -> ( ph <-> th ) )
  assume finds1.4: |- ps
  assume finds1.5: |- ( y e. _om -> ( ch -> th ) )

  disjoint x y
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ph y
  assert |- ( x e. _om -> ph )

  proof
    vx
    cv
    com
    wcel
    c0
    c0
    wceq
    #
    wph
    c0
    eqid
    wph
    wps
    wch
    wth
    @0
    vx
    vy
    finds1.1
    finds1.2
    finds1.3
    wps
    @0
    finds1.4
    a1i
    vy
    cv
    com
    wcel
    wch
    wth
    wi
    @0
    finds1.5
    a1d
    finds2
    mpi
end
