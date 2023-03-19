include "crn.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "c0g.mm"
include "cdm.mm"
include "cfz.mm"
include "wcel.mm"
include "cseq.mm"
include "cuz.mm"
include "wrex.mm"
include "wex.mm"
include "cio.mm"
include "c1.mm"
include "ccnv.mm"
include "cvv.mm"
include "cdif.mm"
include "cima.mm"
include "chash.mm"
include "wf1o.mm"
include "ccom.mm"
include "cif.mm"
include "cgsu.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "sseq2d.mm"
include "eqidd.mm"
include "oveqdr.mm"
include "grpidpropd.mm"
include "seqeq2d.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "exbidv.mm"
include "iotabidv.mm"
include "wb.mm"
include "difeq2d.mm"
include "imaeq2d.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "f1oeq2.mm"
include "syl.mm"
include "f1oeq3.mm"
include "bitrd.mm"
include "fveq12d.mm"
include "ifeq12d.mm"
include "ifbieq12d.mm"
include "eqid.mm"
include "gsumvalx.mm"
include "3eqtr4d.mm"

theorem gsumpropd
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  assume gsumpropd.f: |- ( ph -> F e. V )
  assume gsumpropd.g: |- ( ph -> G e. W )
  assume gsumpropd.h: |- ( ph -> H e. X )
  assume gsumpropd.b: |- ( ph -> ( Base ` G ) = ( Base ` H ) )
  assume gsumpropd.p: |- ( ph -> ( +g ` G ) = ( +g ` H ) )


  assert |- ( ph -> ( G gsum F ) = ( H gsum F ) )

  proof
    wph
    cF
    crn
    #
    vs
    cv
    #
    vt
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @2
    wceq
    #
    @2
    @1
    @3
    co
    #
    @2
    wceq
    #
    wa
    #
    vt
    cG
    cbs
    cfv
    #
    wral
    #
    vs
    @9
    crab
    #
    wss
    #
    cG
    c0g
    cfv
    #
    cF
    cdm
    #
    cfz
    crn
    wcel
    #
    @14
    vm
    cv
    #
    vn
    cv
    #
    cfz
    co
    wceq
    #
    vx
    cv
    #
    @17
    @3
    cF
    @16
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vn
    @16
    cuz
    cfv
    #
    wrex
    #
    vm
    wex
    #
    vx
    cio
    #
    c1
    cF
    ccnv
    #
    cvv
    @11
    cdif
    #
    cima
    #
    chash
    cfv
    #
    cfz
    co
    #
    @30
    vf
    cv
    #
    wf1o
    #
    @19
    @31
    @3
    cF
    @33
    ccom
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vx
    cio
    #
    cif
    #
    cif
    @0
    @1
    @2
    cH
    cplusg
    cfv
    #
    co
    #
    @2
    wceq
    #
    @2
    @1
    @43
    co
    #
    @2
    wceq
    #
    wa
    #
    vt
    cH
    cbs
    cfv
    #
    wral
    #
    vs
    @49
    crab
    #
    wss
    #
    cH
    c0g
    cfv
    #
    @15
    @18
    @19
    @17
    @43
    cF
    @16
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vn
    @24
    wrex
    #
    vm
    wex
    #
    vx
    cio
    #
    c1
    @28
    cvv
    @51
    cdif
    #
    cima
    #
    chash
    cfv
    #
    cfz
    co
    #
    @62
    @33
    wf1o
    #
    @19
    @63
    @43
    @35
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vx
    cio
    #
    cif
    #
    cif
    cG
    cF
    cgsu
    co
    cH
    cF
    cgsu
    co
    wph
    @12
    @52
    @13
    @42
    @53
    @72
    wph
    @11
    @51
    @0
    wph
    @10
    @50
    vs
    @9
    @49
    gsumpropd.b
    wph
    @8
    @48
    vt
    @9
    @49
    gsumpropd.b
    wph
    @5
    @45
    @7
    @47
    wph
    @4
    @44
    @2
    wph
    @3
    @43
    @1
    @2
    gsumpropd.p
    oveqd
    eqeq1d
    wph
    @6
    @46
    @2
    wph
    @3
    @43
    @2
    @1
    gsumpropd.p
    oveqd
    eqeq1d
    anbi12d
    raleqbidv
    rabeqbidv
    #
    sseq2d
    wph
    va
    vb
    @9
    cG
    cH
    wph
    @9
    eqidd
    gsumpropd.b
    wph
    va
    cv
    @9
    wcel
    vb
    cv
    @9
    wcel
    wa
    va
    vb
    @3
    @43
    gsumpropd.p
    oveqdr
    grpidpropd
    wph
    @15
    @27
    @60
    @41
    @71
    wph
    @26
    @59
    vx
    wph
    @25
    @58
    vm
    wph
    @23
    @57
    vn
    @24
    wph
    @22
    @56
    @18
    wph
    @21
    @55
    @19
    wph
    @17
    @20
    @54
    wph
    @3
    @43
    cF
    @16
    gsumpropd.p
    seqeq2d
    fveq1d
    eqeq2d
    anbi2d
    rexbidv
    exbidv
    iotabidv
    wph
    @40
    @70
    vx
    wph
    @39
    @69
    vf
    wph
    @34
    @65
    @38
    @68
    wph
    @34
    @64
    @30
    @33
    wf1o
    #
    @65
    wph
    @32
    @64
    wceq
    @34
    @74
    wb
    wph
    @31
    @63
    c1
    cfz
    wph
    @30
    @62
    chash
    wph
    @29
    @61
    @28
    wph
    @11
    @51
    cvv
    @73
    difeq2d
    imaeq2d
    #
    fveq2d
    #
    oveq2d
    @32
    @64
    @30
    @33
    f1oeq2
    syl
    wph
    @30
    @62
    wceq
    @74
    @65
    wb
    @75
    @30
    @62
    @64
    @33
    f1oeq3
    syl
    bitrd
    wph
    @37
    @67
    @19
    wph
    @31
    @63
    @36
    @66
    wph
    @3
    @43
    @35
    c1
    gsumpropd.p
    seqeq2d
    @76
    fveq12d
    eqeq2d
    anbi12d
    exbidv
    iotabidv
    ifeq12d
    ifbieq12d
    wph
    vx
    vt
    @14
    @9
    @3
    vf
    vm
    vn
    cF
    cG
    @11
    cW
    @30
    cV
    @13
    vs
    @9
    eqid
    @13
    eqid
    @3
    eqid
    @11
    eqid
    wph
    @30
    eqidd
    gsumpropd.g
    gsumpropd.f
    wph
    @14
    eqidd
    #
    gsumvalx
    wph
    vx
    vt
    @14
    @49
    @43
    vf
    vm
    vn
    cF
    cH
    @51
    cX
    @62
    cV
    @53
    vs
    @49
    eqid
    @53
    eqid
    @43
    eqid
    @51
    eqid
    wph
    @62
    eqidd
    gsumpropd.h
    gsumpropd.f
    @77
    gsumvalx
    3eqtr4d
end
