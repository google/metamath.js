include "cfn.mm"
include "wcel.mm"
include "cword.mm"
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
include "wa.mm"
include "c0.mm"
include "cs1.mm"
include "cconcat.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "hasheq0.mm"
include "ax-mp.mm"
include "biimpri.mm"
include "oveq2d.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "fveq1.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "oveq2.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "fveq2.mm"
include "cid.mm"
include "cres.mm"
include "c0g.mm"
include "symgid.mm"
include "adantr.mm"
include "eqid.mm"
include "gsum0.mm"
include "syl6reqr.mm"
include "fvresi.mm"
include "adantl.mm"
include "eqtrd.mm"
include "a1d.mm"
include "c1.mm"
include "caddc.mm"
include "ccatws1len.mm"
include "raleqdv.mm"
include "gsmsymgrfixlem1.mm"
include "3expb.mm"
include "sylbid.mm"
include "exp32.mm"
include "a2d.mm"
include "wrdind.mm"
include "com12.mm"
include "3impia.mm"

theorem gsmsymgrfix
  let cB: class B
  let cS: class S
  let vi: setvar i
  let cK: class K
  let cN: class N
  let cW: class W
  let cP: class P
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume gsmsymgrfix.s: |- S = ( SymGrp ` N )
  assume gsmsymgrfix.b: |- B = ( Base ` S )

  disjoint B i
  disjoint K i
  disjoint N i
  disjoint W i
  disjoint P i
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint i w
  disjoint i y
  disjoint i z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint N w
  disjoint N y
  disjoint N z
  disjoint S w
  disjoint S y
  disjoint S z
  disjoint W w
  assert |- ( ( N e. Fin /\ K e. N /\ W e. Word B ) -> ( A. i e. ( 0 ..^ ( # ` W ) ) ( ( W ` i ) ` K ) = K -> ( ( S gsum W ) ` K ) = K ) )

  proof
    cN
    cfn
    wcel
    #
    cK
    cN
    wcel
    #
    cW
    cB
    cword
    #
    wcel
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
    @3
    @0
    @1
    wa
    #
    @14
    @15
    cK
    @4
    vw
    cv
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
    @16
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
    @16
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
    wi
    @15
    cK
    @4
    c0
    cfv
    #
    cfv
    #
    cK
    wceq
    #
    vi
    c0
    wral
    #
    cK
    cS
    c0
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
    wi
    @15
    cK
    @4
    vy
    cv
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
    @35
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
    @35
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
    wi
    @15
    cK
    @4
    @35
    vz
    cv
    #
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
    @47
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
    @47
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
    wi
    @15
    @14
    wi
    vw
    vy
    vz
    cW
    cB
    @16
    c0
    wceq
    #
    @26
    @34
    @15
    @58
    @22
    @30
    @25
    @33
    @58
    @19
    @29
    vi
    @21
    c0
    @58
    @21
    cc0
    cc0
    cfzo
    co
    c0
    @58
    @20
    cc0
    cc0
    cfzo
    @20
    cc0
    wceq
    #
    @58
    @16
    cvv
    wcel
    @59
    @58
    wb
    vw
    vex
    @16
    cvv
    hasheq0
    ax-mp
    biimpri
    oveq2d
    cc0
    fzo0
    syl6eq
    @58
    @18
    @28
    cK
    @58
    cK
    @17
    @27
    @4
    @16
    c0
    fveq1
    fveq1d
    eqeq1d
    raleqbidv
    @58
    @24
    @32
    cK
    @58
    cK
    @23
    @31
    @16
    c0
    cS
    cgsu
    oveq2
    fveq1d
    eqeq1d
    imbi12d
    imbi2d
    vw
    vy
    weq
    #
    @26
    @45
    @15
    @60
    @22
    @41
    @25
    @44
    @60
    @19
    @38
    vi
    @21
    @40
    @60
    @20
    @39
    cc0
    cfzo
    @16
    @35
    chash
    fveq2
    oveq2d
    @60
    @18
    @37
    cK
    @60
    cK
    @17
    @36
    @4
    @16
    @35
    fveq1
    fveq1d
    eqeq1d
    raleqbidv
    @60
    @24
    @43
    cK
    @60
    cK
    @23
    @42
    @16
    @35
    cS
    cgsu
    oveq2
    fveq1d
    eqeq1d
    imbi12d
    imbi2d
    @16
    @47
    wceq
    #
    @26
    @57
    @15
    @61
    @22
    @53
    @25
    @56
    @61
    @19
    @50
    vi
    @21
    @52
    @61
    @20
    @51
    cc0
    cfzo
    @16
    @47
    chash
    fveq2
    oveq2d
    @61
    @18
    @49
    cK
    @61
    cK
    @17
    @48
    @4
    @16
    @47
    fveq1
    fveq1d
    eqeq1d
    raleqbidv
    @61
    @24
    @55
    cK
    @61
    cK
    @23
    @54
    @16
    @47
    cS
    cgsu
    oveq2
    fveq1d
    eqeq1d
    imbi12d
    imbi2d
    @16
    cW
    wceq
    #
    @26
    @14
    @15
    @62
    @22
    @10
    @25
    @13
    @62
    @19
    @7
    vi
    @21
    @9
    @62
    @20
    @8
    cc0
    cfzo
    @16
    cW
    chash
    fveq2
    oveq2d
    @62
    @18
    @6
    cK
    @62
    cK
    @17
    @5
    @4
    @16
    cW
    fveq1
    fveq1d
    eqeq1d
    raleqbidv
    @62
    @24
    @12
    cK
    @62
    cK
    @23
    @11
    @16
    cW
    cS
    cgsu
    oveq2
    fveq1d
    eqeq1d
    imbi12d
    imbi2d
    @15
    @33
    @30
    @15
    @32
    cK
    cid
    cN
    cres
    #
    cfv
    #
    cK
    @15
    cK
    @31
    @63
    @15
    @63
    cS
    c0g
    cfv
    #
    @31
    @0
    @63
    @65
    wceq
    @1
    cN
    cS
    cfn
    gsmsymgrfix.s
    symgid
    adantr
    cS
    @65
    @65
    eqid
    gsum0
    syl6reqr
    fveq1d
    @1
    @64
    cK
    wceq
    @0
    cN
    cK
    fvresi
    adantl
    eqtrd
    a1d
    @35
    @2
    wcel
    #
    @46
    cB
    wcel
    #
    wa
    #
    @15
    @45
    @57
    @68
    @15
    @45
    @57
    @68
    @15
    @45
    wa
    #
    wa
    @53
    @50
    vi
    cc0
    @39
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wral
    #
    @56
    @68
    @53
    @72
    wb
    #
    @69
    @66
    @73
    @67
    @66
    @50
    vi
    @52
    @71
    @66
    @51
    @70
    cc0
    cfzo
    cB
    @35
    @46
    ccatws1len
    oveq2d
    raleqdv
    adantr
    adantr
    @68
    @15
    @45
    @72
    @56
    wi
    cB
    @46
    cS
    vi
    cK
    cN
    @35
    gsmsymgrfix.s
    gsmsymgrfix.b
    gsmsymgrfixlem1
    3expb
    sylbid
    exp32
    a2d
    wrdind
    com12
    3impia
end
