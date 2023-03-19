include "wsb.mm"
include "wi.mm"
include "sbrim.mm"
include "nfim1.mm"
include "weq.mm"
include "wb.mm"
include "com12.mm"
include "pm5.74d.mm"
include "sbie.mm"
include "bitr3i.mm"
include "pm5.74ri.mm"

theorem sbied
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume sbied.1: |- F/ x ph
  assume sbied.2: |- ( ph -> F/ x ch )
  assume sbied.3: |- ( ph -> ( x = y -> ( ps <-> ch ) ) )


  assert |- ( ph -> ( [ y / x ] ps <-> ch ) )

  proof
    wph
    wps
    vx
    vy
    wsb
    #
    wch
    wph
    @0
    wi
    wph
    wps
    wi
    #
    vx
    vy
    wsb
    wph
    wch
    wi
    #
    wph
    wps
    vx
    vy
    sbied.1
    sbrim
    @1
    @2
    vx
    vy
    wph
    wch
    vx
    sbied.1
    sbied.2
    nfim1
    vx
    vy
    weq
    #
    wph
    wps
    wch
    wph
    @3
    wps
    wch
    wb
    sbied.3
    com12
    pm5.74d
    sbie
    bitr3i
    pm5.74ri
end
