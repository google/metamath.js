include "wcel.mm"
include "char.mm"
include "cfv.mm"
include "cv.mm"
include "cdm.mm"
include "wss.mm"
include "cid.mm"
include "cres.mm"
include "cxp.mm"
include "w3a.mm"
include "cdif.mm"
include "wwe.mm"
include "wa.mm"
include "coi.mm"
include "wceq.mm"
include "copab.mm"
include "cwdom.mm"
include "wbr.mm"
include "cpw.mm"
include "cvv.mm"
include "wfo.mm"
include "wfun.mm"
include "crn.mm"
include "cdom.mm"
include "con0.mm"
include "crab.mm"
include "wi.mm"
include "cep.mm"
include "wrex.mm"
include "eqid.mm"
include "hartogslem1.mm"
include "simp2i.mm"
include "simp1i.mm"
include "sqxpexg.mm"
include "pwexg.mm"
include "syl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "funex.mm"
include "wfn.mm"
include "funfn.mm"
include "mpbi.mm"
include "a1i.mm"
include "simp3i.mm"
include "harval.mm"
include "eqtr4d.mm"
include "df-fo.mm"
include "sylanbrc.mm"
include "fowdom.mm"
include "syl2anc.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "domwdom.mm"
include "wdomtr.mm"

theorem harwdom
  let cV: class V
  let cX: class X
  let vr: setvar r
  let vy: setvar y
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z


  assert |- ( X e. V -> ( har ` X ) ~<_* ~P ( X X. X ) )

  proof
    cX
    cV
    wcel
    #
    cX
    char
    cfv
    #
    vr
    cv
    #
    cdm
    #
    cX
    wss
    cid
    @3
    cres
    @2
    wss
    @2
    @3
    @3
    cxp
    wss
    w3a
    @3
    @2
    cid
    cdif
    #
    wwe
    wa
    vy
    cv
    #
    @3
    @4
    coi
    cdm
    wceq
    wa
    vr
    vy
    copab
    #
    cdm
    #
    cwdom
    wbr
    #
    @7
    cX
    cX
    cxp
    #
    cpw
    #
    cwdom
    wbr
    #
    @1
    @10
    cwdom
    wbr
    @0
    @6
    cvv
    wcel
    #
    @7
    @1
    @6
    wfo
    #
    @8
    @0
    @6
    wfun
    #
    @7
    cvv
    wcel
    #
    @12
    @7
    @10
    wss
    #
    @14
    @0
    @6
    crn
    #
    vx
    cv
    cX
    cdom
    wbr
    vx
    con0
    crab
    #
    wceq
    wi
    #
    vx
    vy
    vz
    vw
    vt
    cX
    vs
    cv
    vw
    cv
    #
    vf
    cv
    #
    cfv
    wceq
    vt
    cv
    vz
    cv
    #
    @21
    cfv
    wceq
    wa
    @20
    @22
    cep
    wbr
    wa
    vz
    @5
    wrex
    vw
    @5
    wrex
    vs
    vt
    copab
    #
    vf
    @6
    cV
    vs
    vr
    @6
    eqid
    @23
    eqid
    hartogslem1
    #
    simp2i
    #
    @0
    @16
    @10
    cvv
    wcel
    #
    @15
    @16
    @14
    @19
    @24
    simp1i
    #
    @0
    @9
    cvv
    wcel
    @26
    cX
    cV
    sqxpexg
    @9
    cvv
    pwexg
    syl
    #
    @7
    @10
    cvv
    ssexg
    sylancr
    cvv
    @6
    funex
    sylancr
    @0
    @6
    @7
    wfn
    #
    @17
    @1
    wceq
    @13
    @29
    @0
    @14
    @29
    @25
    @6
    funfn
    mpbi
    a1i
    @0
    @17
    @18
    @1
    @16
    @14
    @19
    @24
    simp3i
    vx
    cV
    cX
    harval
    eqtr4d
    @7
    @1
    @6
    df-fo
    sylanbrc
    @6
    cvv
    @1
    @7
    fowdom
    syl2anc
    @0
    @7
    @10
    cdom
    wbr
    #
    @11
    @0
    @26
    @16
    @30
    @28
    @27
    @7
    @10
    cvv
    ssdomg
    mpisyl
    @7
    @10
    domwdom
    syl
    @1
    @7
    @10
    wdomtr
    syl2anc
end
