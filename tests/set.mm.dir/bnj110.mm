include "wfr.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "cv.mm"
include "wsbc.mm"
include "crab.mm"
include "wrex.mm"
include "ralnex.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "vex.mm"
include "sbcng.mm"
include "ax-mp.mm"
include "bicomi.mm"
include "ralbii.mm"
include "bitr3i.mm"
include "cab.mm"
include "df-rab.mm"
include "eleq2i.mm"
include "df-sbc.mm"
include "sbcan.mm"
include "sbcel1v.mm"
include "anbi1i.mm"
include "bitri.mm"
include "simprbi.mm"
include "mprgbir.mm"
include "wbr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "rabex.mm"
include "biantrur.mm"
include "rexnal.mm"
include "rabn0.mm"
include "ssrab2.mm"
include "fri.mm"
include "syl2anb.mm"
include "eqid.mm"
include "bnj23.mm"
include "wal.mm"
include "df-ral.mm"
include "sbcbii.mm"
include "sbcal.mm"
include "sbcimg.mm"
include "nfv.mm"
include "sbcgf.mm"
include "csb.mm"
include "sbcbr2g.mm"
include "wceq.mm"
include "csbvarg.mm"
include "breq2i.mm"
include "nfsbc1v.mm"
include "imbi12i.mm"
include "albii.mm"
include "3bitr4i.mm"
include "sylibr.mm"
include "bnj31.mm"
include "nfim.mm"
include "weq.mm"
include "sbceq1a.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "elrabi.mm"
include "imim1i.mm"
include "ralimi2.mm"
include "sylbi.mm"
include "rexim.mm"
include "syl.mm"
include "mpan9.mm"
include "an32s.mm"
include "mto.mm"
include "iman.mm"
include "mpbir.mm"

theorem bnj110
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vz: setvar z
  let vw: setvar w
  assume bnj110.1: |- A e. _V
  assume bnj110.2: |- ( ps <-> A. y e. A ( y R x -> [. y / x ]. ph ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint ph y
  disjoint A z
  disjoint A w
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint R z
  disjoint R w
  disjoint ph z
  disjoint ph w
  disjoint ps z
  assert |- ( ( R Fr A /\ A. x e. A ( ps -> ph ) ) -> A. x e. A ph )

  proof
    cA
    cR
    wfr
    #
    wps
    wph
    wi
    #
    vx
    cA
    wral
    #
    wa
    #
    wph
    vx
    cA
    wral
    #
    wi
    @3
    @4
    wn
    #
    wa
    #
    wn
    @6
    wph
    vx
    vz
    cv
    #
    wsbc
    #
    vz
    wph
    wn
    #
    vx
    cA
    crab
    #
    wrex
    #
    @11
    wn
    #
    @9
    vx
    @7
    wsbc
    #
    vz
    @10
    @12
    @8
    wn
    #
    vz
    @10
    wral
    @13
    vz
    @10
    wral
    @8
    vz
    @10
    ralnex
    @14
    @13
    vz
    @10
    @13
    @14
    @7
    cvv
    wcel
    #
    @13
    @14
    wb
    vz
    vex
    #
    wph
    vx
    @7
    cvv
    sbcng
    ax-mp
    bicomi
    ralbii
    bitr3i
    @7
    @10
    wcel
    #
    @7
    cA
    wcel
    #
    @13
    @17
    @7
    vx
    cv
    #
    cA
    wcel
    #
    @9
    wa
    #
    vx
    cab
    #
    wcel
    #
    @18
    @13
    wa
    #
    @10
    @22
    @7
    @9
    vx
    cA
    df-rab
    eleq2i
    @23
    @21
    vx
    @7
    wsbc
    #
    @24
    @21
    vx
    @7
    df-sbc
    @25
    @20
    vx
    @7
    wsbc
    #
    @13
    wa
    @24
    @20
    @9
    vx
    @7
    sbcan
    @26
    @18
    @13
    vx
    @7
    cA
    sbcel1v
    anbi1i
    bitri
    bitr3i
    bitri
    simprbi
    mprgbir
    @0
    @5
    @2
    @11
    @0
    @5
    wa
    #
    wps
    vx
    @7
    wsbc
    #
    vz
    @10
    wrex
    #
    @2
    @11
    @27
    vw
    cv
    @7
    cR
    wbr
    wn
    vw
    @10
    wral
    #
    @28
    vz
    @10
    @0
    @10
    cvv
    wcel
    #
    @0
    wa
    @10
    cA
    wss
    #
    @10
    c0
    wne
    #
    wa
    #
    @30
    vz
    @10
    wrex
    @5
    @31
    @0
    @9
    vx
    cA
    bnj110.1
    rabex
    biantrur
    @5
    @9
    vx
    cA
    wrex
    #
    @34
    wph
    vx
    cA
    rexnal
    @35
    @33
    @34
    @9
    vx
    cA
    rabn0
    @32
    @33
    @9
    vx
    cA
    ssrab2
    biantrur
    bitr3i
    bitr3i
    vz
    vw
    cA
    @10
    cvv
    cR
    fri
    syl2anb
    @30
    vy
    cv
    #
    @7
    cR
    wbr
    #
    wph
    vx
    @36
    wsbc
    #
    wi
    #
    vy
    cA
    wral
    #
    @28
    wph
    vx
    vz
    vw
    vy
    cA
    @10
    cR
    @10
    eqid
    bnj23
    @36
    @19
    cR
    wbr
    #
    @38
    wi
    #
    vy
    cA
    wral
    #
    vx
    @7
    wsbc
    #
    @36
    cA
    wcel
    #
    @39
    wi
    #
    vy
    wal
    #
    @28
    @40
    @44
    @45
    @42
    wi
    #
    vy
    wal
    #
    vx
    @7
    wsbc
    #
    @47
    @43
    @49
    vx
    @7
    @42
    vy
    cA
    df-ral
    sbcbii
    @50
    @48
    vx
    @7
    wsbc
    #
    vy
    wal
    @47
    @48
    vy
    vx
    @7
    sbcal
    @51
    @46
    vy
    @51
    @45
    vx
    @7
    wsbc
    #
    @42
    vx
    @7
    wsbc
    #
    wi
    #
    @46
    @15
    @51
    @54
    wb
    @16
    @45
    @42
    vx
    @7
    cvv
    sbcimg
    ax-mp
    @52
    @45
    @53
    @39
    @15
    @52
    @45
    wb
    @16
    @45
    vx
    @7
    cvv
    @45
    vx
    nfv
    sbcgf
    ax-mp
    @53
    @41
    vx
    @7
    wsbc
    #
    @38
    vx
    @7
    wsbc
    #
    wi
    #
    @39
    @15
    @53
    @57
    wb
    @16
    @41
    @38
    vx
    @7
    cvv
    sbcimg
    ax-mp
    @55
    @37
    @56
    @38
    @55
    @36
    vx
    @7
    @19
    csb
    #
    cR
    wbr
    #
    @37
    @15
    @55
    @59
    wb
    @16
    vx
    @7
    @36
    @19
    cR
    cvv
    sbcbr2g
    ax-mp
    @58
    @7
    @36
    cR
    @15
    @58
    @7
    wceq
    @16
    vx
    @7
    cvv
    csbvarg
    ax-mp
    breq2i
    bitri
    @15
    @56
    @38
    wb
    @16
    @38
    vx
    @7
    cvv
    wph
    vx
    @36
    nfsbc1v
    sbcgf
    ax-mp
    imbi12i
    bitri
    imbi12i
    bitri
    albii
    bitri
    bitri
    wps
    @43
    vx
    @7
    bnj110.2
    sbcbii
    @39
    vy
    cA
    df-ral
    3bitr4i
    sylibr
    bnj31
    @2
    @28
    @8
    wi
    #
    vz
    @10
    wral
    #
    @29
    @11
    wi
    @2
    @60
    vz
    cA
    wral
    @61
    @1
    @60
    vx
    vz
    cA
    @1
    vz
    nfv
    @28
    @8
    vx
    wps
    vx
    @7
    nfsbc1v
    wph
    vx
    @7
    nfsbc1v
    nfim
    vx
    vz
    weq
    wps
    @28
    wph
    @8
    wps
    vx
    @7
    sbceq1a
    wph
    vx
    @7
    sbceq1a
    imbi12d
    cbvral
    @60
    @60
    vz
    cA
    @10
    @17
    @18
    @60
    @9
    vx
    @7
    cA
    elrabi
    imim1i
    ralimi2
    sylbi
    @28
    @8
    vz
    @10
    rexim
    syl
    mpan9
    an32s
    mto
    @3
    @4
    iman
    mpbir
end
