include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "wreu.mm"
include "wsb.mm"
include "nfv.mm"
include "sb8eu.mm"
include "sban.mm"
include "eubii.mm"
include "clelsb3.mm"
include "anbi1i.mm"
include "nfsb.mm"
include "nfan.mm"
include "weq.mm"
include "eleq1.mm"
include "sbequ.mm"
include "sbie.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "cbveu.mm"
include "bitri.mm"
include "3bitri.mm"
include "df-reu.mm"
include "3bitr4i.mm"

theorem cbvreu
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume cbvral.1: |- F/ y ph
  assume cbvral.2: |- F/ x ps
  assume cbvral.3: |- ( x = y -> ( ph <-> ps ) )

  disjoint A x
  disjoint A y
  disjoint x z
  disjoint A z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( E! x e. A ph <-> E! y e. A ps )

  proof
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vx
    weu
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
    weu
    #
    wph
    vx
    cA
    wreu
    wps
    vy
    cA
    wreu
    @2
    @1
    vx
    vz
    wsb
    #
    vz
    weu
    @0
    vx
    vz
    wsb
    #
    wph
    vx
    vz
    wsb
    #
    wa
    #
    vz
    weu
    #
    @6
    @1
    vx
    vz
    @1
    vz
    nfv
    sb8eu
    @7
    @10
    vz
    @0
    wph
    vx
    vz
    sban
    eubii
    @11
    vz
    cv
    #
    cA
    wcel
    #
    @9
    wa
    #
    vz
    weu
    @6
    @10
    @14
    vz
    @8
    @13
    @9
    vz
    vx
    cA
    clelsb3
    anbi1i
    eubii
    @14
    @5
    vz
    vy
    @13
    @9
    vy
    @13
    vy
    nfv
    wph
    vx
    vz
    vy
    cbvral.1
    nfsb
    nfan
    @5
    vz
    nfv
    vz
    vy
    weq
    #
    @13
    @4
    @9
    wps
    @12
    @3
    cA
    eleq1
    @15
    @9
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
    cbvral.2
    cbvral.3
    sbie
    syl6bb
    anbi12d
    cbveu
    bitri
    3bitri
    wph
    vx
    cA
    df-reu
    wps
    vy
    cA
    df-reu
    3bitr4i
end
