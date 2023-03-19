include "wsbc.mm"
include "cab.mm"
include "wcel.mm"
include "df-sbc.mm"
include "nfabd.mm"
include "nfeld.mm"
include "nfxfrd.mm"

theorem nfsbcd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfsbcd.1: |- F/ y ph
  assume nfsbcd.2: |- ( ph -> F/_ x A )
  assume nfsbcd.3: |- ( ph -> F/ x ps )


  assert |- ( ph -> F/ x [. A / y ]. ps )

  proof
    wps
    vy
    cA
    wsbc
    cA
    wps
    vy
    cab
    #
    wcel
    wph
    vx
    wps
    vy
    cA
    df-sbc
    wph
    vx
    cA
    @0
    nfsbcd.2
    wph
    wps
    vx
    vy
    nfsbcd.1
    nfsbcd.3
    nfabd
    nfeld
    nfxfrd
end
