include "cif.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "cab.mm"
include "dfif2.mm"
include "nfv.mm"
include "nfcrd.mm"
include "nfimd.mm"
include "nfand.mm"
include "nfabd.mm"
include "nfcxfrd.mm"

theorem nfifd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume nfifd.2: |- ( ph -> F/ x ps )
  assume nfifd.3: |- ( ph -> F/_ x A )
  assume nfifd.4: |- ( ph -> F/_ x B )


  assert |- ( ph -> F/_ x if ( ps , A , B ) )

  proof
    wph
    vx
    wps
    cA
    cB
    cif
    vy
    cv
    #
    cB
    wcel
    #
    wps
    wi
    #
    @0
    cA
    wcel
    #
    wps
    wa
    #
    wi
    #
    vy
    cab
    wps
    vy
    cA
    cB
    dfif2
    wph
    @5
    vx
    vy
    wph
    vy
    nfv
    wph
    @2
    @4
    vx
    wph
    @1
    wps
    vx
    wph
    vx
    vy
    cB
    nfifd.4
    nfcrd
    nfifd.2
    nfimd
    wph
    @3
    wps
    vx
    wph
    vx
    vy
    cA
    nfifd.3
    nfcrd
    nfifd.2
    nfand
    nfimd
    nfabd
    nfcxfrd
end
