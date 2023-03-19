include "ctpos.mm"
include "coprab.mm"
include "cv.mm"
include "cop.mm"
include "wbr.mm"
include "tposeqi.mm"
include "cdm.mm"
include "wrel.mm"
include "wceq.mm"
include "reldmoprab.mm"
include "dftpos3.mm"
include "ax-mp.mm"
include "nfcv.mm"
include "nfoprab2.mm"
include "nfbr.mm"
include "nfoprab1.mm"
include "nfv.mm"
include "weq.mm"
include "wa.mm"
include "opeq12.mm"
include "ancoms.mm"
include "breq1d.mm"
include "cbvoprab12.mm"
include "nfoprab3.mm"
include "breq2.mm"
include "wcel.mm"
include "df-br.mm"
include "oprabid.mm"
include "bitri.mm"
include "syl6bb.mm"
include "cbvoprab3.mm"
include "eqtri.mm"
include "3eqtri.mm"

theorem tposoprab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume tposoprab.1: |- F = { <. <. x , y >. , z >. | ph }

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  assert |- tpos F = { <. <. y , x >. , z >. | ph }

  proof
    cF
    ctpos
    wph
    vx
    vy
    vz
    coprab
    #
    ctpos
    #
    vb
    cv
    #
    va
    cv
    #
    cop
    #
    vc
    cv
    #
    @0
    wbr
    #
    va
    vb
    vc
    coprab
    #
    wph
    vy
    vx
    vz
    coprab
    #
    cF
    @0
    tposoprab.1
    tposeqi
    @0
    cdm
    wrel
    @1
    @7
    wceq
    wph
    vx
    vy
    vz
    reldmoprab
    va
    vb
    vc
    @0
    dftpos3
    ax-mp
    @7
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @5
    @0
    wbr
    #
    vy
    vx
    vc
    coprab
    @8
    @6
    @12
    va
    vb
    vc
    vy
    vx
    vy
    @4
    @5
    @0
    vy
    @4
    nfcv
    wph
    vx
    vy
    vz
    nfoprab2
    vy
    @5
    nfcv
    nfbr
    vx
    @4
    @5
    @0
    vx
    @4
    nfcv
    wph
    vx
    vy
    vz
    nfoprab1
    vx
    @5
    nfcv
    nfbr
    @12
    va
    nfv
    @12
    vb
    nfv
    va
    vy
    weq
    #
    vb
    vx
    weq
    #
    wa
    @4
    @11
    @5
    @0
    @14
    @13
    @4
    @11
    wceq
    @2
    @3
    @9
    @10
    opeq12
    ancoms
    breq1d
    cbvoprab12
    @12
    wph
    vy
    vx
    vc
    vz
    vz
    @11
    @5
    @0
    vz
    @11
    nfcv
    wph
    vx
    vy
    vz
    nfoprab3
    vz
    @5
    nfcv
    nfbr
    wph
    vc
    nfv
    vc
    vz
    weq
    @12
    @11
    vz
    cv
    #
    @0
    wbr
    #
    wph
    @5
    @15
    @11
    @0
    breq2
    @16
    @11
    @15
    cop
    @0
    wcel
    wph
    @11
    @15
    @0
    df-br
    wph
    vx
    vy
    vz
    oprabid
    bitri
    syl6bb
    cbvoprab3
    eqtri
    3eqtri
end
