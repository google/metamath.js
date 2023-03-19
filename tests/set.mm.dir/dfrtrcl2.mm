include "crtcl.mm"
include "cfv.mm"
include "crtrcl.mm"
include "wceq.mm"
include "wi.mm"
include "cvv.mm"
include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wss.mm"
include "ccom.mm"
include "w3a.mm"
include "cab.mm"
include "cint.mm"
include "cmpt.mm"
include "eqidd.mm"
include "dmeq.mm"
include "rneq.mm"
include "uneq12d.mm"
include "reseq2d.mm"
include "sseq1d.mm"
include "id.mm"
include "3anbi12d.mm"
include "abbidv.mm"
include "inteqd.mm"
include "adantl.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "cuni.mm"
include "wrel.mm"
include "relfld.mm"
include "syl.mm"
include "eqcomd.mm"
include "rtrclreclem1.mm"
include "syl5ibr.mm"
include "mpcom.mm"
include "rtrclreclem2.mm"
include "rtrclreclem3.mm"
include "wb.mm"
include "wal.mm"
include "fvex.mm"
include "sseq2.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "3anbi123d.mm"
include "a1i.mm"
include "alrimiv.mm"
include "elabgt.mm"
include "sylancr.mm"
include "mpbir3and.mm"
include "ne0i.mm"
include "intex.mm"
include "sylib.mm"
include "fvmptd.mm"
include "intss1.mm"
include "wral.mm"
include "vex.mm"
include "elab.mm"
include "rtrclreclem4.mm"
include "19.21bi.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ssint.mm"
include "sylibr.mm"
include "eqssd.mm"
include "eqtrd.mm"
include "df-rtrcl.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem dfrtrcl2
  let wph: wff ph
  let cR: class R
  let vx: setvar x
  let vz: setvar z
  let vs: setvar s
  assume drrtrcl2.1: |- ( ph -> Rel R )
  assume drrtrcl2.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( t* ` R ) = ( t*rec ` R ) )

  proof
    wph
    cR
    crtcl
    cfv
    #
    cR
    crtrcl
    cfv
    #
    wceq
    #
    wi
    #
    wph
    cR
    vx
    cvv
    cid
    vx
    cv
    #
    cdm
    #
    @4
    crn
    #
    cun
    #
    cres
    #
    vz
    cv
    #
    wss
    #
    @4
    @9
    wss
    #
    @9
    @9
    ccom
    #
    @9
    wss
    #
    w3a
    #
    vz
    cab
    #
    cint
    #
    cmpt
    #
    cfv
    #
    @1
    wceq
    #
    wi
    #
    wph
    @18
    cid
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    cres
    #
    @9
    wss
    #
    cR
    @9
    wss
    #
    @13
    w3a
    #
    vz
    cab
    #
    cint
    #
    @1
    wph
    vx
    cR
    @16
    @29
    cvv
    @17
    cvv
    wph
    @17
    eqidd
    @4
    cR
    wceq
    #
    @16
    @29
    wceq
    wph
    @30
    @15
    @28
    @30
    @14
    @27
    vz
    @30
    @10
    @25
    @11
    @26
    @13
    @30
    @8
    @24
    @9
    @30
    @7
    @23
    cid
    @30
    @5
    @21
    @6
    @22
    @4
    cR
    dmeq
    @4
    cR
    rneq
    uneq12d
    reseq2d
    sseq1d
    @30
    @4
    cR
    @9
    @30
    id
    sseq1d
    3anbi12d
    abbidv
    inteqd
    adantl
    drrtrcl2.2
    wph
    @28
    c0
    wne
    #
    @29
    cvv
    wcel
    wph
    @1
    @28
    wcel
    #
    @31
    wph
    @32
    @24
    @1
    wss
    #
    cR
    @1
    wss
    #
    @1
    @1
    ccom
    #
    @1
    wss
    #
    @23
    cR
    cuni
    cuni
    #
    wceq
    #
    wph
    @33
    wph
    @37
    @23
    wph
    cR
    wrel
    @37
    @23
    wceq
    drrtrcl2.1
    cR
    relfld
    syl
    eqcomd
    wph
    @33
    @38
    cid
    @37
    cres
    #
    @1
    wss
    wph
    cR
    drrtrcl2.1
    drrtrcl2.2
    rtrclreclem1
    @38
    @24
    @39
    @1
    @38
    @23
    @37
    cid
    @38
    id
    reseq2d
    sseq1d
    syl5ibr
    mpcom
    wph
    cR
    drrtrcl2.2
    rtrclreclem2
    wph
    cR
    drrtrcl2.1
    drrtrcl2.2
    rtrclreclem3
    wph
    @1
    cvv
    wcel
    @9
    @1
    wceq
    #
    @27
    @33
    @34
    @36
    w3a
    #
    wb
    wi
    #
    vz
    wal
    @32
    @41
    wb
    cR
    crtrcl
    fvex
    wph
    @42
    vz
    @42
    wph
    @40
    @25
    @33
    @26
    @34
    @13
    @36
    @9
    @1
    @24
    sseq2
    @9
    @1
    cR
    sseq2
    @40
    @12
    @35
    @9
    @1
    @40
    @9
    @1
    @9
    @1
    @40
    id
    #
    @43
    coeq12d
    @43
    sseq12d
    3anbi123d
    a1i
    alrimiv
    @27
    @41
    vz
    @1
    cvv
    elabgt
    sylancr
    mpbir3and
    #
    @28
    @1
    ne0i
    syl
    @28
    intex
    sylib
    fvmptd
    wph
    @29
    @1
    wph
    @32
    @29
    @1
    wss
    @44
    @1
    @28
    intss1
    syl
    wph
    @1
    vs
    cv
    #
    wss
    #
    vs
    @28
    wral
    @1
    @29
    wss
    wph
    @46
    vs
    @28
    @45
    @28
    wcel
    @24
    @45
    wss
    #
    cR
    @45
    wss
    #
    @45
    @45
    ccom
    #
    @45
    wss
    #
    w3a
    #
    wph
    @46
    @27
    @51
    vz
    @45
    vs
    vex
    @9
    @45
    wceq
    #
    @25
    @47
    @26
    @48
    @13
    @50
    @9
    @45
    @24
    sseq2
    @9
    @45
    cR
    sseq2
    @52
    @12
    @49
    @9
    @45
    @52
    @9
    @45
    @9
    @45
    @52
    id
    #
    @53
    coeq12d
    @53
    sseq12d
    3anbi123d
    elab
    wph
    @51
    @46
    wi
    vs
    wph
    cR
    vs
    drrtrcl2.1
    drrtrcl2.2
    rtrclreclem4
    19.21bi
    syl5bi
    ralrimiv
    vs
    @1
    @28
    ssint
    sylibr
    eqssd
    eqtrd
    crtcl
    @17
    wceq
    #
    @3
    @20
    wb
    vx
    vz
    df-rtrcl
    @54
    @2
    @19
    wph
    @54
    @0
    @18
    @1
    cR
    crtcl
    @17
    fveq1
    eqeq1d
    imbi2d
    ax-mp
    mpbir
end
