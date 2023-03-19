include "wcel.mm"
include "cfbas.mm"
include "cfv.mm"
include "w3a.mm"
include "wf.mm"
include "wa.mm"
include "ccom.mm"
include "cfm.mm"
include "co.mm"
include "cv.mm"
include "wss.mm"
include "cima.mm"
include "wrex.mm"
include "wi.mm"
include "cfg.mm"
include "simpl3.mm"
include "ssfg.mm"
include "syl.mm"
include "sseld.mm"
include "simpl2.mm"
include "simprr.mm"
include "eqid.mm"
include "imaelfm.mm"
include "ex.mm"
include "syl3anc.mm"
include "syld.mm"
include "imp.mm"
include "wceq.mm"
include "imaeq2.mm"
include "imaco.mm"
include "syl6eqr.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "rexlimdva.mm"
include "wb.mm"
include "elfm.mm"
include "sstr2.mm"
include "imass2.mm"
include "syl5eqss.mm"
include "syl11.mm"
include "reximdv.mm"
include "com12.mm"
include "adantl.mm"
include "syl6bi.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "anbi2d.mm"
include "simpl1.mm"
include "fco.mm"
include "cfil.mm"
include "fmfil.mm"
include "filfbas.mm"
include "simprl.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem fmco
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y


  assert |- ( ( ( X e. V /\ Y e. W /\ B e. ( fBas ` Z ) ) /\ ( F : Y --> X /\ G : Z --> Y ) ) -> ( ( X FilMap ( F o. G ) ) ` B ) = ( ( X FilMap F ) ` ( ( Y FilMap G ) ` B ) ) )

  proof
    cX
    cV
    wcel
    #
    cY
    cW
    wcel
    #
    cB
    cZ
    cfbas
    cfv
    wcel
    #
    w3a
    #
    cY
    cX
    cF
    wf
    #
    cZ
    cY
    cG
    wf
    #
    wa
    #
    wa
    #
    vs
    cB
    cX
    cF
    cG
    ccom
    #
    cfm
    co
    cfv
    #
    cB
    cY
    cG
    cfm
    co
    cfv
    #
    cX
    cF
    cfm
    co
    cfv
    #
    @7
    vs
    cv
    #
    cX
    wss
    #
    @8
    vu
    cv
    #
    cima
    #
    @12
    wss
    #
    vu
    cB
    wrex
    #
    wa
    #
    @13
    cF
    vt
    cv
    #
    cima
    #
    @12
    wss
    #
    vt
    @10
    wrex
    #
    wa
    #
    @12
    @9
    wcel
    #
    @12
    @11
    wcel
    #
    @7
    @17
    @22
    @13
    @7
    @17
    @22
    @7
    @16
    @22
    vu
    cB
    @7
    @14
    cB
    wcel
    #
    wa
    cG
    @14
    cima
    #
    @10
    wcel
    #
    @16
    @22
    wi
    @7
    @26
    @28
    @7
    @26
    @14
    cZ
    cB
    cfg
    co
    #
    wcel
    #
    @28
    @7
    cB
    @29
    @14
    @7
    @2
    cB
    @29
    wss
    @0
    @1
    @2
    @6
    simpl3
    #
    cB
    cZ
    ssfg
    syl
    sseld
    @7
    @1
    @2
    @5
    @30
    @28
    wi
    @0
    @1
    @2
    @6
    simpl2
    #
    @31
    @3
    @4
    @5
    simprr
    #
    @1
    @2
    @5
    w3a
    @30
    @28
    cW
    cB
    @14
    cG
    @29
    cY
    cZ
    @29
    eqid
    imaelfm
    ex
    syl3anc
    syld
    imp
    @28
    @16
    @22
    @21
    @16
    vt
    @27
    @10
    @19
    @27
    wceq
    #
    @20
    @15
    @12
    @34
    @20
    cF
    @27
    cima
    #
    @15
    @19
    @27
    cF
    imaeq2
    cF
    cG
    @14
    imaco
    #
    syl6eqr
    sseq1d
    rspcev
    ex
    syl
    rexlimdva
    @7
    @21
    @17
    vt
    @10
    @7
    @19
    @10
    wcel
    #
    @19
    cY
    wss
    #
    @27
    @19
    wss
    #
    vu
    cB
    wrex
    #
    wa
    #
    @21
    @17
    wi
    #
    @7
    @1
    @2
    @5
    @37
    @41
    wb
    @32
    @31
    @33
    vu
    @19
    cB
    cW
    cG
    cY
    cZ
    elfm
    syl3anc
    @40
    @42
    @38
    @21
    @40
    @17
    @21
    @39
    @16
    vu
    cB
    @15
    @20
    wss
    @21
    @16
    @39
    @15
    @20
    @12
    sstr2
    @39
    @15
    @35
    @20
    @36
    @27
    @19
    cF
    imass2
    syl5eqss
    syl11
    reximdv
    com12
    adantl
    syl6bi
    rexlimdv
    impbid
    anbi2d
    @7
    @0
    @2
    cZ
    cX
    @8
    wf
    #
    @24
    @18
    wb
    @0
    @1
    @2
    @6
    simpl1
    #
    @31
    @6
    @43
    @3
    cZ
    cY
    cX
    cF
    cG
    fco
    adantl
    vu
    @12
    cB
    cV
    @8
    cX
    cZ
    elfm
    syl3anc
    @7
    @0
    @10
    cY
    cfbas
    cfv
    wcel
    #
    @4
    @25
    @23
    wb
    @44
    @7
    @10
    cY
    cfil
    cfv
    wcel
    #
    @45
    @7
    @1
    @2
    @5
    @46
    @32
    @31
    @33
    cW
    cB
    cG
    cY
    cZ
    fmfil
    syl3anc
    @10
    cY
    filfbas
    syl
    @3
    @4
    @5
    simprl
    vt
    @12
    @10
    cV
    cF
    cX
    cY
    elfm
    syl3anc
    3bitr4d
    eqrdv
end
