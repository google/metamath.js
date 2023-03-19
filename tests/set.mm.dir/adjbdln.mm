include "cbo.mm"
include "wcel.mm"
include "cado.mm"
include "cfv.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "crio.mm"
include "cmap.mm"
include "cdm.mm"
include "bdopadj.mm"
include "adjval.mm"
include "syl.mm"
include "wrex.mm"
include "wreu.mm"
include "clo.mm"
include "ccop.mm"
include "cin.mm"
include "cnlnadj.mm"
include "lncnopbd.mm"
include "lncnbd.mm"
include "rexeqi.mm"
include "3imtr3i.mm"
include "wa.mm"
include "wf.mm"
include "wb.mm"
include "bdopf.mm"
include "adjsym.mm"
include "syl2an.mm"
include "eqcom.mm"
include "2ralbii.mm"
include "syl6bbr.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "adjeu.mm"
include "mpbid.mm"
include "wss.mm"
include "wi.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "sylibr.mm"
include "ssriv.mm"
include "id.mm"
include "rgenw.mm"
include "riotass2.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "a1i.mm"
include "reuss.mm"
include "syl3anc.mm"
include "riotacl.mm"
include "eqeltrd.mm"

theorem adjbdln
  let cT: class T
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. BndLinOp -> ( adjh ` T ) e. BndLinOp )

  proof
    cT
    cbo
    wcel
    #
    cT
    cado
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    csp
    co
    @2
    vt
    cv
    #
    cfv
    @3
    csp
    co
    wceq
    vy
    chil
    wral
    vx
    chil
    wral
    #
    vt
    cbo
    crio
    #
    cbo
    @0
    @1
    @5
    vt
    chil
    chil
    cmap
    co
    #
    crio
    #
    @6
    @0
    cT
    cado
    cdm
    wcel
    #
    @1
    @8
    wceq
    cT
    bdopadj
    #
    vx
    vy
    vt
    cT
    adjval
    syl
    @0
    @5
    vt
    cbo
    wrex
    #
    @5
    vt
    @7
    wreu
    #
    @6
    @8
    wceq
    #
    @0
    @11
    @2
    cT
    cfv
    @3
    csp
    co
    #
    @2
    @3
    @4
    cfv
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    vt
    cbo
    wrex
    #
    cT
    clo
    ccop
    cin
    #
    wcel
    @17
    vt
    @19
    wrex
    @0
    @18
    vx
    vy
    vt
    cT
    cnlnadj
    cT
    lncnopbd
    @17
    vt
    @19
    cbo
    lncnbd
    rexeqi
    3imtr3i
    @0
    @5
    @17
    vt
    cbo
    @0
    @4
    cbo
    wcel
    #
    wa
    @5
    @15
    @14
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    @17
    @0
    chil
    chil
    cT
    wf
    #
    chil
    chil
    @4
    wf
    #
    @5
    @22
    wb
    @20
    cT
    bdopf
    #
    @4
    bdopf
    #
    vx
    vy
    cT
    @4
    adjsym
    syl2an
    @16
    @21
    vx
    vy
    chil
    chil
    @14
    @15
    eqcom
    2ralbii
    syl6bbr
    rexbidva
    mpbird
    #
    @0
    @9
    @12
    @10
    @0
    @23
    @9
    @12
    wb
    @25
    vx
    vy
    vt
    cT
    adjeu
    syl
    mpbid
    #
    cbo
    @7
    wss
    #
    @5
    @5
    wi
    #
    vt
    cbo
    wral
    @11
    @12
    wa
    @13
    vt
    cbo
    @7
    @20
    @24
    @4
    @7
    wcel
    @26
    chil
    chil
    @4
    ax-hilex
    ax-hilex
    elmap
    sylibr
    ssriv
    #
    @30
    vt
    cbo
    @5
    id
    rgenw
    @5
    @5
    vt
    cbo
    @7
    riotass2
    mpanl12
    syl2anc
    eqtr4d
    @0
    @5
    vt
    cbo
    wreu
    #
    @6
    cbo
    wcel
    @0
    @29
    @11
    @12
    @32
    @29
    @0
    @31
    a1i
    @27
    @28
    @5
    vt
    cbo
    @7
    reuss
    syl3anc
    @5
    vt
    cbo
    riotacl
    syl
    eqeltrd
end
