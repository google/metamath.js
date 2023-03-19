include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "cword.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cgsu.mm"
include "co.mm"
include "w3a.mm"
include "csymg.mm"
include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cexp.mm"
include "wi.mm"
include "wral.mm"
include "cc0.mm"
include "cfzo.mm"
include "wrex.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "oveq2d.mm"
include "fveq1.mm"
include "fveq1d.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "rspccv.mm"
include "pmtrdifwrdel2.mm"
include "syl11.mm"
include "3ad2ant1.mm"
include "com12.mm"
include "ad2antlr.mm"
include "imp.mm"
include "oveq2.mm"
include "adantr.mm"
include "ad3antlr.mm"
include "simplll.mm"
include "simprr3.mm"
include "simplrl.mm"
include "3simpa.mm"
include "adantl.mm"
include "simplrr.mm"
include "psgndiflemB.mm"
include "imp31.mm"
include "eqcomd.mm"
include "syl23anc.mm"
include "id.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "psgnuni.mm"
include "ex.mm"
include "rexlimiva.mm"
include "mpcom.mm"

theorem psgndiflemA
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cK: class K
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vq: setvar q
  let vw: setvar w
  let vk: setvar k
  let vi: setvar i
  let vn: setvar n
  let vr: setvar r
  assume psgnfix.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume psgnfix.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume psgnfix.s: |- S = ( SymGrp ` ( N \ { K } ) )
  assume psgnfix.z: |- Z = ( SymGrp ` N )
  assume psgnfix.r: |- R = ran ( pmTrsp ` N )

  disjoint K q
  disjoint P q
  disjoint Q q
  disjoint K w
  disjoint N w
  disjoint Q w
  disjoint S w
  disjoint T w
  disjoint R w
  disjoint Z w
  disjoint k q
  disjoint K i
  disjoint K k
  disjoint K n
  disjoint i k
  disjoint i n
  disjoint k n
  disjoint N i
  disjoint N k
  disjoint N n
  disjoint P k
  disjoint Q k
  disjoint R k
  disjoint S i
  disjoint S k
  disjoint S n
  disjoint T k
  disjoint U i
  disjoint U k
  disjoint U n
  disjoint W i
  disjoint W k
  disjoint W n
  disjoint Z i
  disjoint Z k
  disjoint Z n
  disjoint K r
  disjoint N r
  disjoint P r
  disjoint Q r
  disjoint q r
  disjoint R i
  disjoint R r
  disjoint i r
  disjoint S r
  disjoint U r
  disjoint T i
  disjoint T n
  disjoint T r
  disjoint n r
  disjoint W r
  disjoint W w
  disjoint i w
  disjoint n w
  disjoint r w
  assert |- ( ( ( N e. Fin /\ K e. N ) /\ Q e. { q e. P | ( q ` K ) = K } ) -> ( ( W e. Word T /\ ( Q |` ( N \ { K } ) ) = ( S gsum W ) /\ U e. Word R ) -> ( Q = ( ( SymGrp ` N ) gsum U ) -> ( -u 1 ^ ( # ` W ) ) = ( -u 1 ^ ( # ` U ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    cQ
    cK
    vq
    cv
    cfv
    cK
    wceq
    vq
    cP
    crab
    wcel
    #
    wa
    #
    cW
    cT
    cword
    #
    wcel
    #
    cQ
    cN
    cK
    csn
    cdif
    #
    cres
    cS
    cW
    cgsu
    co
    wceq
    #
    cU
    cR
    cword
    #
    wcel
    #
    w3a
    #
    cQ
    cN
    csymg
    cfv
    #
    cU
    cgsu
    co
    #
    wceq
    #
    c1
    cneg
    #
    cW
    chash
    cfv
    #
    cexp
    co
    #
    @14
    cU
    chash
    cfv
    cexp
    co
    #
    wceq
    #
    wi
    #
    @15
    vr
    cv
    #
    chash
    cfv
    #
    wceq
    #
    cK
    vi
    cv
    #
    @20
    cfv
    #
    cfv
    cK
    wceq
    #
    vn
    cv
    #
    @23
    cW
    cfv
    #
    cfv
    #
    @26
    @24
    cfv
    #
    wceq
    #
    vn
    @6
    wral
    #
    wa
    #
    vi
    cc0
    @15
    cfzo
    co
    #
    wral
    #
    wa
    #
    vr
    @8
    wrex
    #
    @3
    @10
    wa
    #
    @19
    @3
    @10
    @36
    @1
    @10
    @36
    wi
    @0
    @2
    @10
    @1
    @36
    @5
    @7
    @1
    @36
    wi
    @9
    vw
    cv
    #
    chash
    cfv
    #
    @21
    wceq
    #
    @25
    @26
    @23
    @38
    cfv
    #
    cfv
    #
    @29
    wceq
    #
    vn
    @6
    wral
    #
    wa
    #
    vi
    cc0
    @39
    cfzo
    co
    #
    wral
    #
    wa
    #
    vr
    @8
    wrex
    #
    vw
    @4
    wral
    @5
    @36
    @1
    @49
    @36
    vw
    cW
    @4
    @38
    cW
    wceq
    #
    @48
    @35
    vr
    @8
    @50
    @40
    @22
    @47
    @34
    @50
    @39
    @15
    @21
    @38
    cW
    chash
    fveq2
    #
    eqeq1d
    @50
    @45
    @32
    vi
    @46
    @33
    @50
    @39
    @15
    cc0
    cfzo
    @51
    oveq2d
    @50
    @44
    @31
    @25
    @50
    @43
    @30
    vn
    @6
    @50
    @42
    @28
    @29
    @50
    @26
    @41
    @27
    @23
    @38
    cW
    fveq1
    fveq1d
    eqeq1d
    ralbidv
    anbi2d
    raleqbidv
    anbi12d
    rexbidv
    rspccv
    vn
    vw
    vr
    cR
    cT
    vi
    cK
    cN
    psgnfix.t
    psgnfix.r
    pmtrdifwrdel2
    syl11
    3ad2ant1
    com12
    ad2antlr
    imp
    @35
    @37
    @19
    wi
    vr
    @8
    @20
    @8
    wcel
    #
    @35
    wa
    #
    @37
    @19
    @53
    @37
    wa
    #
    @13
    @18
    @54
    @13
    wa
    #
    @16
    @14
    @21
    cexp
    co
    #
    @17
    @35
    @16
    @56
    wceq
    #
    @52
    @37
    @13
    @22
    @57
    @34
    @15
    @21
    @14
    cexp
    oveq2
    adantr
    ad3antlr
    @55
    cN
    cR
    cZ
    cfn
    @20
    cU
    psgnfix.z
    psgnfix.r
    @37
    @0
    @53
    @13
    @0
    @1
    @2
    @10
    simplll
    ad2antlr
    @52
    @35
    @37
    @13
    simplll
    #
    @54
    @9
    @13
    @5
    @7
    @9
    @3
    @53
    simprr3
    adantr
    @55
    cZ
    @20
    cgsu
    co
    #
    cQ
    cZ
    cU
    cgsu
    co
    #
    @55
    @3
    @5
    @7
    wa
    #
    @52
    @22
    @34
    @59
    cQ
    wceq
    @53
    @3
    @10
    @13
    simplrl
    @37
    @61
    @53
    @13
    @10
    @61
    @3
    @5
    @7
    @9
    3simpa
    adantl
    ad2antlr
    @58
    @54
    @22
    @13
    @52
    @22
    @34
    @37
    simplrl
    adantr
    @54
    @34
    @13
    @52
    @22
    @34
    @37
    simplrr
    adantr
    @3
    @61
    wa
    @52
    @22
    @34
    w3a
    #
    wa
    cQ
    @59
    @3
    @61
    @62
    cQ
    @59
    wceq
    cP
    cQ
    cR
    cS
    cT
    @20
    vi
    vn
    cK
    cN
    cW
    cZ
    vq
    psgnfix.p
    psgnfix.t
    psgnfix.s
    psgnfix.z
    psgnfix.r
    psgndiflemB
    imp31
    eqcomd
    syl23anc
    @13
    cQ
    @60
    wceq
    @54
    @13
    cQ
    @12
    @60
    @13
    id
    @11
    cZ
    cU
    cgsu
    cZ
    @11
    psgnfix.z
    eqcomi
    oveq1i
    syl6eq
    adantl
    eqtrd
    psgnuni
    eqtrd
    ex
    ex
    rexlimiva
    mpcom
    ex
end
