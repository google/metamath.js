include "wsb.mm"
include "c0.mm"
include "wsbc.mm"
include "cv.mm"
include "csuc.mm"
include "dfsbcq2.mm"
include "sbequ.mm"
include "sbequ12r.mm"
include "com.mm"
include "wcel.mm"
include "wi.mm"
include "nfv.mm"
include "nfs1v.mm"
include "nfsbc1v.mm"
include "nfim.mm"
include "weq.mm"
include "eleq1.mm"
include "sbequ12.mm"
include "suceq.mm"
include "sbceq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "finds.mm"

theorem findes
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume findes.1: |- [. (/) / x ]. ph
  assume findes.2: |- ( x e. _om -> ( ph -> [. suc x / x ]. ph ) )


  assert |- ( x e. _om -> ph )

  proof
    wph
    vx
    vz
    wsb
    wph
    vx
    c0
    wsbc
    wph
    vx
    vy
    wsb
    #
    wph
    vx
    vy
    cv
    #
    csuc
    #
    wsbc
    #
    wph
    vz
    vy
    vx
    cv
    #
    wph
    vx
    vz
    c0
    dfsbcq2
    wph
    vz
    vy
    vx
    sbequ
    wph
    vx
    vz
    @2
    dfsbcq2
    wph
    vz
    vx
    sbequ12r
    findes.1
    @4
    com
    wcel
    #
    wph
    wph
    vx
    @4
    csuc
    #
    wsbc
    #
    wi
    #
    wi
    @1
    com
    wcel
    #
    @0
    @3
    wi
    #
    wi
    vx
    vy
    @9
    @10
    vx
    @9
    vx
    nfv
    @0
    @3
    vx
    wph
    vx
    vy
    nfs1v
    wph
    vx
    @2
    nfsbc1v
    nfim
    nfim
    vx
    vy
    weq
    #
    @5
    @9
    @8
    @10
    @4
    @1
    com
    eleq1
    @11
    wph
    @0
    @7
    @3
    wph
    vx
    vy
    sbequ12
    @11
    wph
    vx
    @6
    @2
    @4
    @1
    suceq
    sbceq1d
    imbi12d
    imbi12d
    findes.2
    chvar
    finds
end
