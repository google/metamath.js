include "cn.mm"
include "wcel.mm"
include "crab.mm"
include "wa.mm"
include "c1.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "wss.mm"
include "1nn.mm"
include "elrab.mm"
include "mpbir2an.mm"
include "elrabi.mm"
include "peano2nn.mm"
include "a1d.mm"
include "anim12d.mm"
include "3imtr4g.mm"
include "mpcom.mm"
include "rgen.mm"
include "nfcv.mm"
include "nfrab.mm"
include "nfv.mm"
include "nfel2.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "cbvralf.mm"
include "mpbi.mm"
include "peano5nni.mm"
include "mp2an.mm"
include "sseli.mm"
include "sylib.mm"
include "simprd.mm"

theorem nnindf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  assume nnindf.x: |- F/ y ph
  assume nnindf.1: |- ( x = 1 -> ( ph <-> ps ) )
  assume nnindf.2: |- ( x = y -> ( ph <-> ch ) )
  assume nnindf.3: |- ( x = ( y + 1 ) -> ( ph <-> th ) )
  assume nnindf.4: |- ( x = A -> ( ph <-> ta ) )
  assume nnindf.5: |- ps
  assume nnindf.6: |- ( y e. NN -> ( ch -> th ) )

  disjoint x y
  disjoint A x
  disjoint ch x
  disjoint ps x
  disjoint ta x
  disjoint th x
  disjoint w x
  disjoint w y
  disjoint ph w
  assert |- ( A e. NN -> ta )

  proof
    cA
    cn
    wcel
    #
    @0
    wta
    @0
    cA
    wph
    vx
    cn
    crab
    #
    wcel
    @0
    wta
    wa
    cn
    @1
    cA
    c1
    @1
    wcel
    #
    vw
    cv
    #
    c1
    caddc
    co
    #
    @1
    wcel
    #
    vw
    @1
    wral
    #
    cn
    @1
    wss
    @2
    c1
    cn
    wcel
    wps
    1nn
    nnindf.5
    wph
    wps
    vx
    c1
    cn
    nnindf.1
    elrab
    mpbir2an
    vy
    cv
    #
    c1
    caddc
    co
    #
    @1
    wcel
    #
    vy
    @1
    wral
    @6
    @9
    vy
    @1
    @7
    cn
    wcel
    #
    @7
    @1
    wcel
    #
    @9
    wph
    vx
    @7
    cn
    elrabi
    @10
    @10
    wch
    wa
    @8
    cn
    wcel
    #
    wth
    wa
    @11
    @9
    @10
    @10
    @12
    wch
    wth
    @10
    @12
    @10
    @7
    peano2nn
    a1d
    nnindf.6
    anim12d
    wph
    wch
    vx
    @7
    cn
    nnindf.2
    elrab
    wph
    wth
    vx
    @8
    cn
    nnindf.3
    elrab
    3imtr4g
    mpcom
    rgen
    @9
    @5
    vy
    vw
    @1
    wph
    vy
    vx
    cn
    nnindf.x
    vy
    cn
    nfcv
    nfrab
    #
    vw
    @1
    nfcv
    @9
    vw
    nfv
    vy
    @4
    @1
    @13
    nfel2
    @7
    @3
    wceq
    @8
    @4
    @1
    @7
    @3
    c1
    caddc
    oveq1
    eleq1d
    cbvralf
    mpbi
    vw
    @1
    peano5nni
    mp2an
    sseli
    wph
    wta
    vx
    cA
    cn
    nnindf.4
    elrab
    sylib
    simprd
end
