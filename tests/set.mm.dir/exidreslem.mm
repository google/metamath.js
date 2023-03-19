include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cdm.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cxp.mm"
include "cres.mm"
include "dmeqi.mm"
include "xpss12.mm"
include "anidms.mm"
include "wfo.mm"
include "wf.mm"
include "opidon2OLD.mm"
include "fof.mm"
include "fdm.mm"
include "3syl.mm"
include "sseq2d.mm"
include "syl5ibr.mm"
include "imp.mm"
include "ssdmres.mm"
include "sylib.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "biimp3ar.mm"
include "ssel2.mm"
include "cmpidelt.mm"
include "sylan2.mm"
include "anassrs.mm"
include "adantrl.mm"
include "wb.mm"
include "oveqi.mm"
include "ovres.mm"
include "eqeq1d.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "adantl.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "3impa.mm"
include "3adant3.mm"
include "raleqdv.mm"
include "jca.mm"

theorem exidreslem
  let vx: setvar x
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vu: setvar u
  assume exidres.1: |- X = ran G
  assume exidres.2: |- U = ( GId ` G )
  assume exidres.3: |- H = ( G |` ( Y X. Y ) )

  disjoint G x
  disjoint Y x
  disjoint X x
  disjoint U x
  disjoint H x
  disjoint U u
  disjoint u x
  disjoint H u
  assert |- ( ( G e. ( Magma i^i ExId ) /\ Y C_ X /\ U e. Y ) -> ( U e. dom dom H /\ A. x e. dom dom H ( ( U H x ) = x /\ ( x H U ) = x ) ) )

  proof
    cG
    cmagm
    cexid
    cin
    wcel
    #
    cY
    cX
    wss
    #
    cU
    cY
    wcel
    #
    w3a
    #
    cU
    cH
    cdm
    #
    cdm
    #
    wcel
    #
    cU
    vx
    cv
    #
    cH
    co
    #
    @7
    wceq
    #
    @7
    cU
    cH
    co
    #
    @7
    wceq
    #
    wa
    #
    vx
    @5
    wral
    #
    @0
    @1
    @6
    @2
    @0
    @1
    wa
    #
    @5
    cY
    cU
    @14
    @5
    cY
    cY
    cxp
    #
    cdm
    #
    cY
    @14
    @4
    @15
    @14
    @4
    cG
    @15
    cres
    #
    cdm
    #
    @15
    cH
    @17
    exidres.3
    dmeqi
    #
    @14
    @15
    cG
    cdm
    #
    wss
    #
    @18
    @15
    wceq
    #
    @0
    @1
    @21
    @1
    @21
    @0
    @15
    cX
    cX
    cxp
    #
    wss
    #
    @1
    @24
    cY
    cX
    cY
    cX
    xpss12
    anidms
    @0
    @20
    @23
    @15
    @0
    @23
    cX
    cG
    wfo
    @23
    cX
    cG
    wf
    @20
    @23
    wceq
    cG
    cX
    exidres.1
    opidon2OLD
    @23
    cX
    cG
    fof
    @23
    cX
    cG
    fdm
    3syl
    sseq2d
    syl5ibr
    imp
    #
    @15
    cG
    ssdmres
    #
    sylib
    syl5eq
    dmeqd
    cY
    dmxpid
    #
    syl6eq
    eleq2d
    biimp3ar
    @3
    @13
    @12
    vx
    cY
    wral
    #
    @0
    @1
    @2
    @28
    @14
    @2
    wa
    @12
    vx
    cY
    @14
    @2
    @7
    cY
    wcel
    #
    @12
    @14
    @2
    @29
    wa
    #
    wa
    @12
    cU
    @7
    cG
    co
    #
    @7
    wceq
    #
    @7
    cU
    cG
    co
    #
    @7
    wceq
    #
    wa
    #
    @14
    @29
    @35
    @2
    @0
    @1
    @29
    @35
    @1
    @29
    wa
    @0
    @7
    cX
    wcel
    @35
    cY
    cX
    @7
    ssel2
    @7
    cU
    cG
    cX
    exidres.1
    exidres.2
    cmpidelt
    sylan2
    anassrs
    adantrl
    @30
    @12
    @35
    wb
    @14
    @30
    @9
    @32
    @11
    @34
    @30
    @8
    @31
    @7
    @30
    @8
    cU
    @7
    @17
    co
    @31
    cH
    @17
    cU
    @7
    exidres.3
    oveqi
    cU
    @7
    cY
    cY
    cG
    ovres
    syl5eq
    eqeq1d
    @30
    @10
    @33
    @7
    @29
    @2
    @10
    @33
    wceq
    @29
    @2
    wa
    @10
    @7
    cU
    @17
    co
    @33
    cH
    @17
    @7
    cU
    exidres.3
    oveqi
    @7
    cU
    cY
    cY
    cG
    ovres
    syl5eq
    ancoms
    eqeq1d
    anbi12d
    adantl
    mpbird
    anassrs
    ralrimiva
    3impa
    @3
    @12
    vx
    @5
    cY
    @3
    @5
    @16
    cY
    @3
    @4
    @15
    @3
    @4
    @18
    @15
    @19
    @3
    @21
    @22
    @0
    @1
    @21
    @2
    @25
    3adant3
    @26
    sylib
    syl5eq
    dmeqd
    @27
    syl6eq
    raleqdv
    mpbird
    jca
end
