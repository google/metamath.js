include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "ccom.mm"
include "cfv.mm"
include "necom.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "cpr.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "simp1.mm"
include "3ad2ant2.mm"
include "simp2.mm"
include "prssi.mm"
include "syl2anc.mm"
include "3jca.mm"
include "pr2nelem.mm"
include "syl.mm"
include "pmtrf.mm"
include "feq1i.mm"
include "sylibr.mm"
include "ffn.mm"
include "fvco2.mm"
include "fveq1i.mm"
include "pmtrprfv.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "simp3.mm"
include "3eqtrd.mm"
include "id.mm"
include "3anrot.mm"
include "biid.mm"
include "3anbi123i.mm"
include "sylbbr.mm"
include "pmtrprfv3.mm"
include "syl3an.mm"
include "3netr4d.mm"

theorem pmtr3ncomlem1
  let cD: class D
  let cT: class T
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume pmtr3ncom.t: |- T = ( pmTrsp ` D )
  assume pmtr3ncom.f: |- F = ( T ` { X , Y } )
  assume pmtr3ncom.g: |- G = ( T ` { Y , Z } )


  assert |- ( ( D e. V /\ ( X e. D /\ Y e. D /\ Z e. D ) /\ ( X =/= Y /\ X =/= Z /\ Y =/= Z ) ) -> ( ( G o. F ) ` X ) =/= ( ( F o. G ) ` X ) )

  proof
    cD
    cV
    wcel
    #
    cX
    cD
    wcel
    #
    cY
    cD
    wcel
    #
    cZ
    cD
    wcel
    #
    w3a
    #
    cX
    cY
    wne
    #
    cX
    cZ
    wne
    #
    cY
    cZ
    wne
    #
    w3a
    #
    w3a
    #
    cZ
    cY
    cX
    cG
    cF
    ccom
    cfv
    #
    cX
    cF
    cG
    ccom
    cfv
    #
    @8
    @0
    cZ
    cY
    wne
    #
    @4
    @7
    @5
    @12
    @6
    @7
    @12
    cY
    cZ
    necom
    biimpi
    3ad2ant3
    3ad2ant3
    @9
    @10
    cX
    cF
    cfv
    #
    cG
    cfv
    #
    cY
    cG
    cfv
    #
    cZ
    @9
    cF
    cD
    wfn
    #
    @1
    @10
    @14
    wceq
    @9
    cD
    cD
    cF
    wf
    #
    @16
    @9
    cD
    cD
    cX
    cY
    cpr
    #
    cT
    cfv
    #
    wf
    #
    @17
    @9
    @0
    @18
    cD
    wss
    #
    @18
    c2o
    cen
    wbr
    #
    w3a
    @20
    @9
    @0
    @21
    @22
    @0
    @4
    @8
    simp1
    #
    @9
    @1
    @2
    @21
    @4
    @0
    @1
    @8
    @1
    @2
    @3
    simp1
    3ad2ant2
    #
    @4
    @0
    @2
    @8
    @1
    @2
    @3
    simp2
    #
    3ad2ant2
    #
    cX
    cY
    cD
    prssi
    syl2anc
    @9
    @1
    @2
    @5
    w3a
    #
    @22
    @9
    @1
    @2
    @5
    @24
    @26
    @8
    @0
    @5
    @4
    @5
    @6
    @7
    simp1
    3ad2ant3
    3jca
    #
    cX
    cY
    cD
    cD
    pr2nelem
    syl
    3jca
    cD
    @18
    cT
    cV
    pmtr3ncom.t
    pmtrf
    syl
    cD
    cD
    cF
    @19
    pmtr3ncom.f
    feq1i
    sylibr
    cD
    cD
    cF
    ffn
    syl
    @24
    cD
    cG
    cF
    cX
    fvco2
    syl2anc
    @9
    @13
    cY
    cG
    @9
    @13
    cX
    @19
    cfv
    #
    cY
    cX
    cF
    @19
    pmtr3ncom.f
    fveq1i
    @9
    @0
    @27
    @29
    cY
    wceq
    @23
    @28
    cD
    cT
    cV
    cX
    cY
    pmtr3ncom.t
    pmtrprfv
    syl2anc
    syl5eq
    #
    fveq2d
    @9
    @15
    cY
    cY
    cZ
    cpr
    #
    cT
    cfv
    #
    cfv
    #
    cZ
    cY
    cG
    @32
    pmtr3ncom.g
    fveq1i
    @9
    @0
    @2
    @3
    @7
    w3a
    #
    @33
    cZ
    wceq
    @23
    @9
    @2
    @3
    @7
    @26
    @4
    @0
    @3
    @8
    @1
    @2
    @3
    simp3
    #
    3ad2ant2
    @8
    @0
    @7
    @4
    @5
    @6
    @7
    simp3
    3ad2ant3
    3jca
    #
    cD
    cT
    cV
    cY
    cZ
    pmtr3ncom.t
    pmtrprfv
    syl2anc
    syl5eq
    3eqtrd
    @9
    @11
    cX
    cG
    cfv
    #
    cF
    cfv
    #
    @13
    cY
    @9
    cG
    cD
    wfn
    #
    @1
    @11
    @38
    wceq
    @9
    cD
    cD
    cG
    wf
    #
    @39
    @9
    @0
    @31
    cD
    wss
    #
    @31
    c2o
    cen
    wbr
    #
    w3a
    #
    @40
    @9
    @0
    @41
    @42
    @23
    @4
    @0
    @41
    @8
    @4
    @2
    @3
    @41
    @25
    @35
    cY
    cZ
    cD
    prssi
    syl2anc
    3ad2ant2
    @9
    @34
    @42
    @36
    cY
    cZ
    cD
    cD
    pr2nelem
    syl
    3jca
    @43
    cD
    cD
    @32
    wf
    @40
    cD
    @31
    cT
    cV
    pmtr3ncom.t
    pmtrf
    cD
    cD
    cG
    @32
    pmtr3ncom.g
    feq1i
    sylibr
    syl
    cD
    cD
    cG
    ffn
    syl
    @24
    cD
    cF
    cG
    cX
    fvco2
    syl2anc
    @9
    @37
    cX
    cF
    @9
    @37
    cX
    @32
    cfv
    #
    cX
    cX
    cG
    @32
    pmtr3ncom.g
    fveq1i
    @0
    @0
    @4
    @2
    @3
    @1
    w3a
    #
    @8
    @7
    cY
    cX
    wne
    #
    cZ
    cX
    wne
    #
    w3a
    #
    @44
    cX
    wceq
    @0
    id
    @4
    @45
    @1
    @2
    @3
    3anrot
    biimpi
    @48
    @46
    @47
    @7
    w3a
    @8
    @7
    @46
    @47
    3anrot
    @46
    @5
    @47
    @6
    @7
    @7
    cY
    cX
    necom
    cZ
    cX
    necom
    @7
    biid
    3anbi123i
    sylbbr
    cD
    cT
    cV
    cY
    cZ
    cX
    pmtr3ncom.t
    pmtrprfv3
    syl3an
    syl5eq
    fveq2d
    @30
    3eqtrd
    3netr4d
end
