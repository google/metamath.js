include "cioo.mm"
include "cxp.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "ctb.mm"
include "crn.mm"
include "iooex.mm"
include "rnex.mm"
include "imassrn.mm"
include "ssexi.mm"
include "co.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cxr.mm"
include "wceq.mm"
include "sseli.mm"
include "anim12i.mm"
include "iooin.mm"
include "syl2an.mm"
include "ifcl.mm"
include "ancoms.mm"
include "cop.mm"
include "cfv.mm"
include "df-ov.mm"
include "opelxpi.mm"
include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wi.mm"
include "cr.mm"
include "cpw.mm"
include "wf.mm"
include "ioof.mm"
include "ffun.mm"
include "ax-mp.mm"
include "xpss12.mm"
include "mp2an.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "funfvima2.mm"
include "syl.mm"
include "syl5eqel.mm"
include "an4s.mm"
include "eqeltrd.mm"
include "ralrimivva.mm"
include "rgen2a.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "ralima.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "ineq1d.mm"
include "ineq2.mm"
include "ineq2d.mm"
include "ralxp.mm"
include "bitri.mm"
include "syl6bb.mm"
include "mpbir.mm"
include "fiinbas.mm"

theorem qtopbaslem
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume qtopbas.1: |- S C_ RR*


  assert |- ( (,) " ( S X. S ) ) e. TopBases

  proof
    cioo
    cS
    cS
    cxp
    #
    cima
    #
    cvv
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    @1
    wcel
    #
    vy
    @1
    wral
    #
    vx
    @1
    wral
    #
    @1
    ctb
    wcel
    @1
    cioo
    crn
    cioo
    iooex
    rnex
    cioo
    @0
    imassrn
    ssexi
    @7
    vz
    cv
    #
    vw
    cv
    #
    cioo
    co
    #
    vv
    cv
    #
    vu
    cv
    #
    cioo
    co
    #
    cin
    #
    @1
    wcel
    #
    vu
    cS
    wral
    vv
    cS
    wral
    #
    vw
    cS
    wral
    vz
    cS
    wral
    #
    @16
    vz
    vw
    cS
    @8
    cS
    wcel
    #
    @9
    cS
    wcel
    #
    wa
    #
    @15
    vv
    vu
    cS
    cS
    @20
    @11
    cS
    wcel
    #
    @12
    cS
    wcel
    #
    wa
    #
    wa
    @14
    @8
    @11
    cle
    wbr
    #
    @11
    @8
    cif
    #
    @9
    @12
    cle
    wbr
    #
    @9
    @12
    cif
    #
    cioo
    co
    #
    @1
    @20
    @8
    cxr
    wcel
    #
    @9
    cxr
    wcel
    #
    wa
    @11
    cxr
    wcel
    #
    @12
    cxr
    wcel
    #
    wa
    @14
    @28
    wceq
    @23
    @18
    @29
    @19
    @30
    cS
    cxr
    @8
    qtopbas.1
    sseli
    cS
    cxr
    @9
    qtopbas.1
    sseli
    anim12i
    @21
    @31
    @22
    @32
    cS
    cxr
    @11
    qtopbas.1
    sseli
    cS
    cxr
    @12
    qtopbas.1
    sseli
    anim12i
    @8
    @9
    @11
    @12
    iooin
    syl2an
    @18
    @21
    @19
    @22
    @28
    @1
    wcel
    #
    @18
    @21
    wa
    @25
    cS
    wcel
    #
    @27
    cS
    wcel
    #
    @33
    @19
    @22
    wa
    @21
    @18
    @34
    @24
    @11
    @8
    cS
    ifcl
    ancoms
    @26
    @9
    @12
    cS
    ifcl
    @34
    @35
    wa
    #
    @28
    @25
    @27
    cop
    #
    cioo
    cfv
    #
    @1
    @25
    @27
    cioo
    df-ov
    @36
    @37
    @0
    wcel
    #
    @38
    @1
    wcel
    #
    @25
    @27
    cS
    cS
    opelxpi
    cioo
    wfun
    #
    @0
    cioo
    cdm
    #
    wss
    @39
    @40
    wi
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    #
    @41
    ioof
    @43
    @44
    cioo
    ffun
    ax-mp
    @0
    @43
    @42
    cS
    cxr
    wss
    #
    @46
    @0
    @43
    wss
    #
    qtopbas.1
    qtopbas.1
    cS
    cxr
    cS
    cxr
    xpss12
    mp2an
    #
    @43
    @44
    cioo
    ioof
    fdmi
    sseqtr4i
    @0
    @37
    cioo
    funfvima2
    mp2an
    syl
    syl5eqel
    syl2an
    an4s
    eqeltrd
    ralrimivva
    rgen2a
    @7
    vt
    cv
    #
    cioo
    cfv
    #
    @3
    cin
    #
    @1
    wcel
    #
    vy
    @1
    wral
    #
    vt
    @0
    wral
    #
    @17
    cioo
    @43
    wfn
    #
    @47
    @7
    @54
    wb
    @45
    @55
    ioof
    @43
    @44
    cioo
    ffn
    ax-mp
    #
    @48
    @6
    @53
    vx
    vt
    @43
    @0
    cioo
    @2
    @50
    wceq
    #
    @5
    @52
    vy
    @1
    @57
    @4
    @51
    @1
    @2
    @50
    @3
    ineq1
    eleq1d
    ralbidv
    ralima
    mp2an
    @53
    @16
    vt
    vz
    vw
    cS
    cS
    @49
    @8
    @9
    cop
    #
    wceq
    #
    @53
    @10
    @3
    cin
    #
    @1
    wcel
    #
    vy
    @1
    wral
    #
    @16
    @59
    @52
    @61
    vy
    @1
    @59
    @51
    @60
    @1
    @59
    @50
    @10
    @3
    @59
    @50
    @58
    cioo
    cfv
    @10
    @49
    @58
    cioo
    fveq2
    @8
    @9
    cioo
    df-ov
    syl6eqr
    ineq1d
    eleq1d
    ralbidv
    @62
    @10
    @50
    cin
    #
    @1
    wcel
    #
    vt
    @0
    wral
    #
    @16
    @55
    @47
    @62
    @65
    wb
    @56
    @48
    @61
    @64
    vy
    vt
    @43
    @0
    cioo
    @3
    @50
    wceq
    @60
    @63
    @1
    @3
    @50
    @10
    ineq2
    eleq1d
    ralima
    mp2an
    @64
    @15
    vt
    vv
    vu
    cS
    cS
    @49
    @11
    @12
    cop
    #
    wceq
    #
    @63
    @14
    @1
    @67
    @50
    @13
    @10
    @67
    @50
    @66
    cioo
    cfv
    @13
    @49
    @66
    cioo
    fveq2
    @11
    @12
    cioo
    df-ov
    syl6eqr
    ineq2d
    eleq1d
    ralxp
    bitri
    syl6bb
    ralxp
    bitri
    mpbir
    vx
    vy
    @1
    cvv
    fiinbas
    mp2an
end
