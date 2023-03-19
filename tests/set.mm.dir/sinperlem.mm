include "cc.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ce.mm"
include "cfv.mm"
include "cneg.mm"
include "cdiv.mm"
include "wceq.mm"
include "zcn.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "mulcl.mm"
include "sylancl.mm"
include "ax-icn.mm"
include "adddi.mm"
include "mp3an1.mm"
include "sylan2.mm"
include "mul12.mm"
include "mp3an13.mm"
include "syl.mm"
include "mulcom.mm"
include "eqtrd.mm"
include "adantl.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "mpan.mm"
include "efper.mm"
include "sylan.mm"
include "negicn.mm"
include "negeqd.mm"
include "mulneg1.mm"
include "sylancr.mm"
include "mulneg2.mm"
include "3eqtr4d.mm"
include "znegcl.mm"
include "syl2an.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "addcl.mm"
include "adantr.mm"

theorem sinperlem
  let cA: class A
  let cD: class D
  let cF: class F
  let cK: class K
  let cO: class O
  assume sinperlem.1: |- ( A e. CC -> ( F ` A ) = ( ( ( exp ` ( _i x. A ) ) O ( exp ` ( -u _i x. A ) ) ) / D ) )
  assume sinperlem.2: |- ( ( A + ( K x. ( 2 x. _pi ) ) ) e. CC -> ( F ` ( A + ( K x. ( 2 x. _pi ) ) ) ) = ( ( ( exp ` ( _i x. ( A + ( K x. ( 2 x. _pi ) ) ) ) ) O ( exp ` ( -u _i x. ( A + ( K x. ( 2 x. _pi ) ) ) ) ) ) / D ) )


  assert |- ( ( A e. CC /\ K e. ZZ ) -> ( F ` ( A + ( K x. ( 2 x. _pi ) ) ) ) = ( F ` A ) )

  proof
    cA
    cc
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    ci
    cA
    cK
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    @5
    cmul
    co
    #
    ce
    cfv
    #
    cO
    co
    #
    cD
    cdiv
    co
    #
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    @8
    cA
    cmul
    co
    #
    ce
    cfv
    #
    cO
    co
    #
    cD
    cdiv
    co
    #
    @5
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    @2
    @11
    @17
    cD
    cdiv
    @2
    @7
    @14
    @10
    @16
    cO
    @2
    @7
    @13
    ci
    @3
    cmul
    co
    #
    cK
    cmul
    co
    #
    caddc
    co
    #
    ce
    cfv
    #
    @14
    @2
    @6
    @23
    ce
    @2
    @6
    @13
    ci
    @4
    cmul
    co
    #
    caddc
    co
    #
    @23
    @1
    @0
    @4
    cc
    wcel
    #
    @6
    @26
    wceq
    #
    @1
    cK
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @27
    cK
    zcn
    #
    c2
    cpi
    2cn
    picn
    mulcli
    #
    cK
    @3
    mulcl
    sylancl
    #
    ci
    cc
    wcel
    #
    @0
    @27
    @28
    ax-icn
    ci
    cA
    @4
    adddi
    mp3an1
    sylan2
    @2
    @25
    @22
    @13
    caddc
    @1
    @25
    @22
    wceq
    @0
    @1
    @25
    cK
    @21
    cmul
    co
    #
    @22
    @1
    @29
    @25
    @35
    wceq
    #
    @31
    @34
    @29
    @30
    @36
    ax-icn
    @32
    ci
    cK
    @3
    mul12
    mp3an13
    syl
    @1
    @29
    @21
    cc
    wcel
    #
    @35
    @22
    wceq
    @31
    ci
    @3
    ax-icn
    @32
    mulcli
    #
    cK
    @21
    mulcom
    sylancl
    eqtrd
    #
    adantl
    oveq2d
    eqtrd
    fveq2d
    @0
    @13
    cc
    wcel
    #
    @1
    @24
    @14
    wceq
    @34
    @0
    @40
    ax-icn
    ci
    cA
    mulcl
    mpan
    @13
    cK
    efper
    sylan
    eqtrd
    @2
    @10
    @15
    @21
    cK
    cneg
    #
    cmul
    co
    #
    caddc
    co
    #
    ce
    cfv
    #
    @16
    @2
    @9
    @43
    ce
    @2
    @9
    @15
    @8
    @4
    cmul
    co
    #
    caddc
    co
    #
    @43
    @1
    @0
    @27
    @9
    @46
    wceq
    #
    @33
    @8
    cc
    wcel
    #
    @0
    @27
    @47
    negicn
    @8
    cA
    @4
    adddi
    mp3an1
    sylan2
    @2
    @45
    @42
    @15
    caddc
    @1
    @45
    @42
    wceq
    @0
    @1
    @25
    cneg
    #
    @22
    cneg
    #
    @45
    @42
    @1
    @25
    @22
    @39
    negeqd
    @1
    @34
    @27
    @45
    @49
    wceq
    ax-icn
    @33
    ci
    @4
    mulneg1
    sylancr
    @1
    @37
    @29
    @42
    @50
    wceq
    @38
    @31
    @21
    cK
    mulneg2
    sylancr
    3eqtr4d
    adantl
    oveq2d
    eqtrd
    fveq2d
    @0
    @15
    cc
    wcel
    #
    @41
    cz
    wcel
    @44
    @16
    wceq
    @1
    @48
    @0
    @51
    negicn
    @8
    cA
    mulcl
    mpan
    cK
    znegcl
    @15
    @41
    efper
    syl2an
    eqtrd
    oveq12d
    oveq1d
    @2
    @5
    cc
    wcel
    #
    @19
    @12
    wceq
    @1
    @0
    @27
    @52
    @33
    cA
    @4
    addcl
    sylan2
    sinperlem.2
    syl
    @0
    @20
    @18
    wceq
    @1
    sinperlem.1
    adantr
    3eqtr4d
end
