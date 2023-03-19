include "wcel.mm"
include "cv.mm"
include "ccom.mm"
include "wss.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cun.mm"
include "ccnv.mm"
include "cdif.mm"
include "wceq.mm"
include "wi.mm"
include "cnvco.mm"
include "cnvss.mm"
include "syl5eqssr.mm"
include "coundir.mm"
include "coundi.mm"
include "ssid.mm"
include "c0.mm"
include "cononrel2.mm"
include "0ss.mm"
include "eqsstri.mm"
include "unssi.mm"
include "cononrel1.mm"
include "id.mm"
include "syl5ss.mm"
include "ssun3.mm"
include "3syl.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "syl5ibr.mm"
include "adantl.mm"
include "ssun1.mm"
include "a1i.mm"
include "trclexlem.mm"
include "cossxp.mm"
include "dmxpss.mm"
include "xpss1.mm"
include "ax-mp.mm"
include "sstri.mm"
include "rnxpss.mm"
include "xpss2.mm"
include "xptrrel.mm"
include "ssun2.mm"
include "clcnvlem.mm"

theorem cnvtrcl0
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  let cX: class X

  disjoint x y
  disjoint V x
  disjoint V y
  disjoint X x
  disjoint X y
  assert |- ( X e. V -> `' |^| { x | ( X C_ x /\ ( x o. x ) C_ x ) } = |^| { y | ( `' X C_ y /\ ( y o. y ) C_ y ) } )

  proof
    cX
    cV
    wcel
    #
    vx
    cv
    #
    @1
    ccom
    #
    @1
    wss
    #
    vy
    cv
    #
    @4
    ccom
    #
    @4
    wss
    #
    cX
    cX
    cdm
    #
    cX
    crn
    #
    cxp
    #
    cun
    #
    @10
    ccom
    #
    @10
    wss
    #
    vx
    vy
    @10
    cX
    @1
    @4
    ccnv
    #
    cX
    cX
    ccnv
    ccnv
    cdif
    #
    cun
    #
    wceq
    #
    @6
    @3
    wi
    @0
    @6
    @3
    @16
    @15
    @15
    ccom
    #
    @15
    wss
    #
    @6
    @13
    @13
    ccom
    #
    @13
    wss
    #
    @17
    @13
    wss
    @18
    @6
    @19
    @5
    ccnv
    @13
    @4
    @4
    cnvco
    @5
    @4
    cnvss
    syl5eqssr
    @20
    @17
    @19
    @13
    @17
    @13
    @15
    ccom
    #
    @14
    @15
    ccom
    #
    cun
    @19
    @13
    @14
    @15
    coundir
    @21
    @22
    @19
    @21
    @19
    @13
    @14
    ccom
    #
    cun
    @19
    @13
    @13
    @14
    coundi
    @19
    @23
    @19
    @19
    ssid
    @23
    c0
    @19
    @13
    cX
    cononrel2
    @19
    0ss
    #
    eqsstri
    unssi
    eqsstri
    @22
    c0
    @19
    cX
    @15
    cononrel1
    @24
    eqsstri
    unssi
    eqsstri
    @20
    id
    syl5ss
    @17
    @13
    @14
    ssun3
    3syl
    @16
    @2
    @17
    @1
    @15
    @16
    @1
    @15
    @1
    @15
    @16
    id
    #
    @25
    coeq12d
    @25
    sseq12d
    syl5ibr
    adantl
    @4
    @1
    ccnv
    #
    wceq
    #
    @3
    @6
    wi
    @0
    @3
    @6
    @27
    @26
    @26
    ccom
    #
    @26
    wss
    @3
    @28
    @2
    ccnv
    @26
    @1
    @1
    cnvco
    @2
    @1
    cnvss
    syl5eqssr
    @27
    @5
    @28
    @4
    @26
    @27
    @4
    @26
    @4
    @26
    @27
    id
    #
    @29
    coeq12d
    @29
    sseq12d
    syl5ibr
    adantl
    @1
    @10
    wceq
    #
    @2
    @11
    @1
    @10
    @30
    @1
    @10
    @1
    @10
    @30
    id
    #
    @31
    coeq12d
    @31
    sseq12d
    cX
    @10
    wss
    @0
    cX
    @9
    ssun1
    a1i
    cX
    cV
    trclexlem
    @12
    @0
    @11
    @9
    @10
    @11
    cX
    @10
    ccom
    #
    @9
    @10
    ccom
    #
    cun
    @9
    cX
    @9
    @10
    coundir
    @32
    @33
    @9
    @32
    cX
    cX
    ccom
    #
    cX
    @9
    ccom
    #
    cun
    @9
    cX
    cX
    @9
    coundi
    @34
    @35
    @9
    cX
    cX
    cossxp
    @35
    @9
    cdm
    #
    @8
    cxp
    #
    @9
    cX
    @9
    cossxp
    @36
    @7
    wss
    @37
    @9
    wss
    @7
    @8
    dmxpss
    @36
    @7
    @8
    xpss1
    ax-mp
    sstri
    unssi
    eqsstri
    @33
    @9
    cX
    ccom
    #
    @9
    @9
    ccom
    #
    cun
    @9
    @9
    cX
    @9
    coundi
    @38
    @39
    @9
    @38
    @7
    @9
    crn
    #
    cxp
    #
    @9
    @9
    cX
    cossxp
    @40
    @8
    wss
    @41
    @9
    wss
    @7
    @8
    rnxpss
    @40
    @8
    @7
    xpss2
    ax-mp
    sstri
    @7
    @8
    xptrrel
    unssi
    eqsstri
    unssi
    eqsstri
    @9
    cX
    ssun2
    sstri
    a1i
    clcnvlem
end
