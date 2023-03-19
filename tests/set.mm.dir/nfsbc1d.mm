include "wsbc.mm"
include "cab.mm"
include "wcel.mm"
include "df-sbc.mm"
include "wnfc.mm"
include "nfab1.mm"
include "a1i.mm"
include "nfeld.mm"
include "nfxfrd.mm"

theorem nfsbc1d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume nfsbc1d.2: |- ( ph -> F/_ x A )


  assert |- ( ph -> F/ x [. A / x ]. ps )

  proof
    wps
    vx
    cA
    wsbc
    cA
    wps
    vx
    cab
    #
    wcel
    wph
    vx
    wps
    vx
    cA
    df-sbc
    wph
    vx
    cA
    @0
    nfsbc1d.2
    vx
    @0
    wnfc
    wph
    wps
    vx
    nfab1
    a1i
    nfeld
    nfxfrd
end
