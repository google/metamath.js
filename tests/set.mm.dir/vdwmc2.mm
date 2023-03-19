include "cvdwm.mm"
include "wbr.mm"
include "cv.mm"
include "cvdwa.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "cn.mm"
include "wrex.mm"
include "wex.mm"
include "cmul.mm"
include "caddc.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "vdwmc.mm"
include "wb.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "w3a.mm"
include "vdwapid1.mm"
include "ne0i.mm"
include "syl.mm"
include "3expb.mm"
include "adantll.mm"
include "ssn0.mm"
include "expcom.mm"
include "wn.mm"
include "cin.mm"
include "disjsn.mm"
include "wf.mm"
include "adantr.mm"
include "fimacnvdisj.mm"
include "ex.mm"
include "syl5bir.mm"
include "necon1ad.mm"
include "syld.mm"
include "rexlimdvva.mm"
include "pm4.71rd.mm"
include "exbidv.mm"
include "df-rex.mm"
include "syl6bbr.mm"
include "ffvelrnd.mm"
include "1nn.mm"
include "ne0ii.mm"
include "simpllr.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "vdwap0.mm"
include "eqtrd.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "ralrimiva.mm"
include "r19.2z.mm"
include "sylancr.mm"
include "ralrimivw.mm"
include "syl2anc.mm"
include "rexex.mm"
include "2thd.mm"
include "cn0.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "wal.mm"
include "vdwapval.mm"
include "sylan.mm"
include "imbi1d.mm"
include "albidv.mm"
include "dfss2.mm"
include "ralcom4.mm"
include "ovex.mm"
include "eleq1.mm"
include "ceqsalv.mm"
include "ralbii.mm"
include "r19.23v.mm"
include "albii.mm"
include "3bitr3i.mm"
include "3bitr4g.mm"
include "2rexbidva.mm"
include "rexbidv.mm"
include "3bitrd.mm"

theorem vdwmc2
  let wph: wff ph
  let cA: class A
  let cR: class R
  let vm: setvar m
  let cF: class F
  let cK: class K
  let cX: class X
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let cJ: class J
  let cM: class M
  assume vdwmc.1: |- X e. _V
  assume vdwmc.2: |- ( ph -> K e. NN0 )
  assume vdwmc.3: |- ( ph -> F : X --> R )
  assume vdwmc2.4: |- ( ph -> A e. X )

  disjoint a c
  disjoint a d
  disjoint R a
  disjoint c d
  disjoint R c
  disjoint R d
  disjoint a ph
  disjoint d ph
  disjoint a c
  disjoint a d
  disjoint a m
  disjoint F a
  disjoint c d
  disjoint c m
  disjoint F c
  disjoint d m
  disjoint F d
  disjoint F m
  disjoint K a
  disjoint K c
  disjoint K d
  disjoint K m
  disjoint c ph
  disjoint a f
  disjoint a i
  disjoint a k
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint c f
  disjoint c i
  disjoint c k
  disjoint c w
  disjoint c x
  disjoint c z
  disjoint d f
  disjoint d i
  disjoint d k
  disjoint d w
  disjoint d x
  disjoint d z
  disjoint f i
  disjoint f k
  disjoint f m
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint F f
  disjoint i k
  disjoint i m
  disjoint i w
  disjoint i x
  disjoint i z
  disjoint F i
  disjoint k m
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint m w
  disjoint m x
  disjoint m z
  disjoint w x
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint K f
  disjoint K i
  disjoint K k
  disjoint K w
  disjoint K x
  disjoint K z
  disjoint ph x
  disjoint J d
  disjoint J f
  disjoint J i
  disjoint J k
  disjoint J m
  disjoint M a
  disjoint M d
  disjoint M f
  disjoint M i
  disjoint M k
  disjoint M m
  assert |- ( ph -> ( K MonoAP F <-> E. c e. R E. a e. NN E. d e. NN A. m e. ( 0 ... ( K - 1 ) ) ( a + ( m x. d ) ) e. ( `' F " { c } ) ) )

  proof
    wph
    cK
    cF
    cvdwm
    wbr
    va
    cv
    #
    vd
    cv
    #
    cK
    cvdwa
    cfv
    #
    co
    #
    cF
    ccnv
    vc
    cv
    #
    csn
    #
    cima
    #
    wss
    #
    vd
    cn
    wrex
    #
    va
    cn
    wrex
    #
    vc
    wex
    #
    @9
    vc
    cR
    wrex
    #
    @0
    vm
    cv
    @1
    cmul
    co
    #
    caddc
    co
    #
    @6
    wcel
    #
    vm
    cc0
    cK
    c1
    cmin
    co
    cfz
    co
    #
    wral
    #
    vd
    cn
    wrex
    va
    cn
    wrex
    #
    vc
    cR
    wrex
    wph
    cR
    cF
    cK
    cX
    va
    vc
    vd
    vdwmc.1
    vdwmc.2
    vdwmc.3
    vdwmc
    wph
    cK
    cn
    wcel
    #
    @10
    @11
    wb
    cK
    cc0
    wceq
    #
    wph
    @18
    wa
    #
    @10
    @4
    cR
    wcel
    #
    @9
    wa
    #
    vc
    wex
    @11
    @20
    @9
    @22
    vc
    @20
    @9
    @21
    @20
    @7
    @21
    va
    vd
    cn
    cn
    @20
    @0
    cn
    wcel
    #
    @1
    cn
    wcel
    #
    wa
    #
    wa
    #
    @7
    @6
    c0
    wne
    #
    @21
    @26
    @3
    c0
    wne
    #
    @7
    @27
    wi
    @18
    @25
    @28
    wph
    @18
    @23
    @24
    @28
    @18
    @23
    @24
    w3a
    @0
    @3
    wcel
    @28
    @0
    @1
    cK
    vdwapid1
    @3
    @0
    ne0i
    syl
    3expb
    adantll
    @7
    @28
    @27
    @3
    @6
    ssn0
    expcom
    syl
    @26
    @21
    @6
    c0
    @21
    wn
    cR
    @5
    cin
    c0
    wceq
    #
    @26
    @6
    c0
    wceq
    #
    cR
    @4
    disjsn
    @20
    @29
    @30
    wi
    #
    @25
    @20
    cX
    cR
    cF
    wf
    #
    @31
    wph
    @32
    @18
    vdwmc.3
    adantr
    @32
    @29
    @30
    cX
    cR
    @5
    cF
    fimacnvdisj
    ex
    syl
    adantr
    syl5bir
    necon1ad
    syld
    rexlimdvva
    pm4.71rd
    exbidv
    @9
    vc
    cR
    df-rex
    syl6bbr
    wph
    @19
    wa
    #
    @10
    @11
    @33
    @11
    @10
    @33
    cR
    c0
    wne
    #
    @9
    vc
    cR
    wral
    @11
    wph
    @34
    @19
    wph
    cA
    cF
    cfv
    #
    cR
    wcel
    @34
    wph
    cX
    cR
    cA
    cF
    vdwmc.3
    vdwmc2.4
    ffvelrnd
    cR
    @35
    ne0i
    syl
    adantr
    @33
    @9
    vc
    cR
    @33
    cn
    c0
    wne
    #
    @8
    va
    cn
    wral
    @9
    c1
    cn
    1nn
    ne0ii
    #
    @33
    @8
    va
    cn
    @33
    @23
    wa
    #
    @36
    @7
    vd
    cn
    wral
    @8
    @37
    @38
    @7
    vd
    cn
    @38
    @24
    wa
    #
    @3
    c0
    @6
    @39
    @3
    @0
    @1
    cc0
    cvdwa
    cfv
    #
    co
    #
    c0
    @39
    @2
    @40
    @0
    @1
    @39
    cK
    cc0
    cvdwa
    wph
    @19
    @23
    @24
    simpllr
    fveq2d
    oveqd
    @23
    @24
    @41
    c0
    wceq
    @33
    @0
    @1
    vdwap0
    adantll
    eqtrd
    @6
    0ss
    syl6eqss
    ralrimiva
    @7
    vd
    cn
    r19.2z
    sylancr
    ralrimiva
    @8
    va
    cn
    r19.2z
    sylancr
    ralrimivw
    @9
    vc
    cR
    r19.2z
    syl2anc
    #
    @9
    vc
    cR
    rexex
    syl
    @42
    2thd
    wph
    cK
    cn0
    wcel
    #
    @18
    @19
    wo
    vdwmc.2
    cK
    elnn0
    sylib
    mpjaodan
    wph
    @9
    @17
    vc
    cR
    wph
    @7
    @16
    va
    vd
    cn
    cn
    wph
    @25
    wa
    #
    vx
    cv
    #
    @3
    wcel
    #
    @45
    @6
    wcel
    #
    wi
    #
    vx
    wal
    @45
    @13
    wceq
    #
    vm
    @15
    wrex
    #
    @47
    wi
    #
    vx
    wal
    #
    @7
    @16
    @44
    @48
    @51
    vx
    @44
    @46
    @50
    @47
    wph
    @43
    @25
    @46
    @50
    wb
    #
    vdwmc.2
    @43
    @23
    @24
    @53
    @0
    @1
    vm
    cK
    @45
    vdwapval
    3expb
    sylan
    imbi1d
    albidv
    vx
    @3
    @6
    dfss2
    @49
    @47
    wi
    #
    vx
    wal
    #
    vm
    @15
    wral
    @54
    vm
    @15
    wral
    #
    vx
    wal
    @16
    @52
    @54
    vm
    vx
    @15
    ralcom4
    @55
    @14
    vm
    @15
    @47
    @14
    vx
    @13
    @0
    @12
    caddc
    ovex
    @45
    @13
    @6
    eleq1
    ceqsalv
    ralbii
    @56
    @51
    vx
    @49
    @47
    vm
    @15
    r19.23v
    albii
    3bitr3i
    3bitr4g
    2rexbidva
    rexbidv
    3bitrd
end
