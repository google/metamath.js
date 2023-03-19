include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "cgsu.mm"
include "wi.mm"
include "w3a.mm"
include "cs1.mm"
include "cconcat.mm"
include "c1.mm"
include "caddc.mm"
include "csn.mm"
include "cun.mm"
include "cuz.mm"
include "cn0.mm"
include "lencl.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "fzosplitsn.mm"
include "syl.mm"
include "raleqdv.mm"
include "wb.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "ralunsn.mm"
include "bitrd.mm"
include "simpl.mm"
include "simpr.mm"
include "eqidd.mm"
include "3jca.mm"
include "ccats1val2.mm"
include "3adant3.mm"
include "ccom.mm"
include "adantl.mm"
include "gsumccatsymgsn.mm"
include "wfn.mm"
include "wf.mm"
include "symgbasf.mm"
include "ffn.mm"
include "anim12i.mm"
include "fvco2.mm"
include "ccats1val1.mm"
include "syl3anc.mm"
include "ralbidva.mm"
include "biimpd.mm"
include "adantld.mm"
include "simp3.mm"
include "syld.mm"
include "imp.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "exp32.mm"
include "sylbid.mm"
include "com23.mm"
include "impd.mm"

theorem gsmsymgrfixlem1
  let cB: class B
  let cP: class P
  let cS: class S
  let vi: setvar i
  let cK: class K
  let cN: class N
  let cW: class W
  assume gsmsymgrfix.s: |- S = ( SymGrp ` N )
  assume gsmsymgrfix.b: |- B = ( Base ` S )

  disjoint B i
  disjoint K i
  disjoint N i
  disjoint P i
  disjoint W i
  assert |- ( ( ( W e. Word B /\ P e. B ) /\ ( N e. Fin /\ K e. N ) /\ ( A. i e. ( 0 ..^ ( # ` W ) ) ( ( W ` i ) ` K ) = K -> ( ( S gsum W ) ` K ) = K ) ) -> ( A. i e. ( 0 ..^ ( ( # ` W ) + 1 ) ) ( ( ( W ++ <" P "> ) ` i ) ` K ) = K -> ( ( S gsum ( W ++ <" P "> ) ) ` K ) = K ) )

  proof
    cW
    cB
    cword
    wcel
    #
    cP
    cB
    wcel
    #
    wa
    #
    cN
    cfn
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    #
    cK
    vi
    cv
    #
    cW
    cfv
    #
    cfv
    #
    cK
    wceq
    #
    vi
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    cK
    cS
    cW
    cgsu
    co
    #
    cfv
    #
    cK
    wceq
    #
    wi
    #
    w3a
    #
    cK
    @6
    cW
    cP
    cs1
    cconcat
    co
    #
    cfv
    #
    cfv
    #
    cK
    wceq
    #
    vi
    cc0
    @10
    c1
    caddc
    co
    cfzo
    co
    #
    wral
    #
    @21
    vi
    @11
    wral
    #
    cK
    @10
    @18
    cfv
    #
    cfv
    #
    cK
    wceq
    #
    wa
    #
    cK
    cS
    @18
    cgsu
    co
    #
    cfv
    #
    cK
    wceq
    #
    @17
    @23
    @21
    vi
    @11
    @10
    csn
    cun
    #
    wral
    #
    @28
    @17
    @21
    vi
    @22
    @32
    @17
    @10
    cc0
    cuz
    cfv
    wcel
    #
    @22
    @32
    wceq
    @2
    @5
    @34
    @16
    @0
    @34
    @1
    @0
    @10
    cn0
    wcel
    #
    @34
    cB
    cW
    lencl
    #
    @10
    elnn0uz
    sylib
    adantr
    3ad2ant1
    cc0
    @10
    fzosplitsn
    syl
    raleqdv
    @17
    @35
    @33
    @28
    wb
    @2
    @5
    @35
    @16
    @0
    @35
    @1
    @36
    adantr
    3ad2ant1
    @21
    @27
    vi
    @11
    @10
    cn0
    @6
    @10
    wceq
    #
    @20
    @26
    cK
    @37
    cK
    @19
    @25
    @6
    @10
    @18
    fveq2
    fveq1d
    eqeq1d
    ralunsn
    syl
    bitrd
    @17
    @24
    @27
    @31
    @17
    @27
    @24
    @31
    @17
    @27
    cK
    cP
    cfv
    #
    cK
    wceq
    #
    @24
    @31
    wi
    @2
    @5
    @27
    @39
    wb
    #
    @16
    @2
    @5
    wa
    #
    @0
    @1
    @10
    @10
    wceq
    #
    w3a
    #
    @40
    @2
    @43
    @5
    @2
    @0
    @1
    @42
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    @2
    @10
    eqidd
    3jca
    adantr
    @43
    @26
    @38
    cK
    @43
    cK
    @25
    cP
    cP
    @10
    cB
    cW
    ccats1val2
    fveq1d
    eqeq1d
    syl
    3adant3
    @17
    @39
    @24
    @31
    @17
    @39
    @24
    wa
    #
    wa
    #
    @30
    cK
    @13
    cP
    ccom
    #
    cfv
    #
    @38
    @13
    cfv
    #
    cK
    @47
    @3
    @0
    @1
    w3a
    #
    @30
    @49
    wceq
    @17
    @51
    @46
    @2
    @5
    @51
    @16
    @41
    @3
    @0
    @1
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    @2
    @0
    @5
    @44
    adantr
    #
    @2
    @1
    @5
    @45
    adantr
    #
    3jca
    3adant3
    adantr
    @51
    cK
    @29
    @48
    cN
    cB
    cS
    cfn
    cW
    cP
    gsmsymgrfix.s
    gsmsymgrfix.b
    gsumccatsymgsn
    fveq1d
    syl
    @47
    cP
    cN
    wfn
    #
    @4
    wa
    #
    @49
    @50
    wceq
    @17
    @55
    @46
    @2
    @5
    @55
    @16
    @2
    @54
    @5
    @4
    @1
    @54
    @0
    @1
    cN
    cN
    cP
    wf
    @54
    cN
    cB
    cP
    cS
    gsmsymgrfix.s
    gsmsymgrfix.b
    symgbasf
    cN
    cN
    cP
    ffn
    syl
    adantl
    @3
    @4
    simpr
    anim12i
    3adant3
    adantr
    cN
    @13
    cP
    cK
    fvco2
    syl
    @47
    @50
    @14
    cK
    @46
    @50
    @14
    wceq
    #
    @17
    @39
    @56
    @24
    @38
    cK
    @13
    fveq2
    adantr
    adantl
    @17
    @46
    @15
    @17
    @46
    @12
    @15
    @2
    @5
    @46
    @12
    wi
    @16
    @41
    @24
    @12
    @39
    @41
    @24
    @12
    @41
    @21
    @9
    vi
    @11
    @41
    @6
    @11
    wcel
    #
    wa
    #
    @20
    @8
    cK
    @58
    cK
    @19
    @7
    @58
    @0
    @1
    @57
    @19
    @7
    wceq
    @41
    @0
    @57
    @52
    adantr
    @41
    @1
    @57
    @53
    adantr
    @41
    @57
    simpr
    cP
    @6
    cB
    cW
    ccats1val1
    syl3anc
    fveq1d
    eqeq1d
    ralbidva
    biimpd
    adantld
    3adant3
    @2
    @5
    @16
    simp3
    syld
    imp
    eqtrd
    3eqtrd
    exp32
    sylbid
    com23
    impd
    sylbid
end
