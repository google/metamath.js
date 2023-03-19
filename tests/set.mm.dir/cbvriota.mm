include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "crio.mm"
include "wsb.mm"
include "weq.mm"
include "eleq1.mm"
include "sbequ12.mm"
include "anbi12d.mm"
include "nfv.mm"
include "nfs1v.mm"
include "nfan.mm"
include "cbviota.mm"
include "sbequ.mm"
include "sbie.mm"
include "syl6bb.mm"
include "nfsb.mm"
include "eqtri.mm"
include "df-riota.mm"
include "3eqtr4i.mm"

theorem cbvriota
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume cbvriota.1: |- F/ y ph
  assume cbvriota.2: |- F/ x ps
  assume cbvriota.3: |- ( x = y -> ( ph <-> ps ) )

  disjoint A x
  disjoint A y
  disjoint x z
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( iota_ x e. A ph ) = ( iota_ y e. A ps )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wa
    #
    vx
    cio
    #
    vy
    cv
    #
    cA
    wcel
    #
    wps
    wa
    #
    vy
    cio
    #
    wph
    vx
    cA
    crio
    wps
    vy
    cA
    crio
    @3
    vz
    cv
    #
    cA
    wcel
    #
    wph
    vx
    vz
    wsb
    #
    wa
    #
    vz
    cio
    @7
    @2
    @11
    vx
    vz
    vx
    vz
    weq
    @1
    @9
    wph
    @10
    @0
    @8
    cA
    eleq1
    wph
    vx
    vz
    sbequ12
    anbi12d
    @2
    vz
    nfv
    @9
    @10
    vx
    @9
    vx
    nfv
    wph
    vx
    vz
    nfs1v
    nfan
    cbviota
    @11
    @6
    vz
    vy
    vz
    vy
    weq
    #
    @9
    @5
    @10
    wps
    @8
    @4
    cA
    eleq1
    @12
    @10
    wph
    vx
    vy
    wsb
    wps
    wph
    vz
    vy
    vx
    sbequ
    wph
    wps
    vx
    vy
    cbvriota.2
    cbvriota.3
    sbie
    syl6bb
    anbi12d
    @9
    @10
    vy
    @9
    vy
    nfv
    wph
    vx
    vz
    vy
    cbvriota.1
    nfsb
    nfan
    @6
    vz
    nfv
    cbviota
    eqtri
    wph
    vx
    cA
    df-riota
    wps
    vy
    cA
    df-riota
    3eqtr4i
end
