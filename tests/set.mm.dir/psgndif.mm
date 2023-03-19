include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "csymg.mm"
include "cgsu.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cexp.mm"
include "cpmtr.mm"
include "crn.mm"
include "cword.mm"
include "wrex.mm"
include "cio.mm"
include "eqid.mm"
include "psgnfix2.mm"
include "imp.mm"
include "ad2antrr.mm"
include "wi.mm"
include "w3a.mm"
include "psgndiflemA.mm"
include "3anassrs.mm"
include "adantlrr.mm"
include "wb.mm"
include "eqeq1.mm"
include "ad2antll.mm"
include "adantr.mm"
include "sylibrd.mm"
include "ralrimiva.mm"
include "r19.29imd.mm"
include "ex.mm"
include "rexlimdva.mm"
include "psgnfix1.mm"
include "simp-4l.mm"
include "simpr.mm"
include "simp-4r.mm"
include "3jca.mm"
include "syl3c.mm"
include "eqcomd.mm"
include "impbid.mm"
include "iotabidv.mm"
include "cbs.mm"
include "diffi.mm"
include "symgfixelsi.mm"
include "adantll.mm"
include "psgnvalfi.mm"
include "syl2anc.mm"
include "simpl.mm"
include "elrabi.mm"
include "syl2an.mm"
include "3eqtr4d.mm"

theorem psgndif
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cK: class K
  let cN: class N
  let cZ: class Z
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  assume psgndif.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume psgndif.s: |- S = ( pmSgn ` N )
  assume psgndif.z: |- Z = ( pmSgn ` ( N \ { K } ) )

  disjoint K q
  disjoint P q
  disjoint Q q
  disjoint K r
  disjoint K s
  disjoint K w
  disjoint q r
  disjoint q s
  disjoint q w
  disjoint r s
  disjoint r w
  disjoint s w
  disjoint N r
  disjoint N s
  disjoint N w
  disjoint P r
  disjoint P s
  disjoint P w
  disjoint Q r
  disjoint Q s
  disjoint Q w
  disjoint S r
  disjoint S s
  disjoint Z s
  disjoint Z w
  assert |- ( ( N e. Fin /\ K e. N ) -> ( Q e. { q e. P | ( q ` K ) = K } -> ( Z ` ( Q |` ( N \ { K } ) ) ) = ( S ` Q ) ) )

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
    #
    cQ
    cK
    vq
    cv
    cfv
    cK
    wceq
    #
    vq
    cP
    crab
    #
    wcel
    #
    cQ
    cN
    cK
    csn
    #
    cdif
    #
    cres
    #
    cZ
    cfv
    #
    cQ
    cS
    cfv
    #
    wceq
    @2
    @5
    wa
    #
    @8
    @7
    csymg
    cfv
    #
    vw
    cv
    #
    cgsu
    co
    wceq
    #
    vs
    cv
    #
    c1
    cneg
    #
    @13
    chash
    cfv
    cexp
    co
    #
    wceq
    #
    wa
    #
    vw
    @7
    cpmtr
    cfv
    crn
    #
    cword
    #
    wrex
    #
    vs
    cio
    #
    cQ
    cN
    csymg
    cfv
    #
    vr
    cv
    #
    cgsu
    co
    wceq
    #
    @15
    @16
    @25
    chash
    cfv
    cexp
    co
    #
    wceq
    #
    wa
    #
    vr
    cN
    cpmtr
    cfv
    crn
    #
    cword
    #
    wrex
    #
    vs
    cio
    #
    @9
    @10
    @11
    @22
    @32
    vs
    @11
    @22
    @32
    @11
    @19
    @32
    vw
    @21
    @11
    @13
    @21
    wcel
    #
    wa
    #
    @19
    @32
    @35
    @19
    wa
    #
    @26
    @28
    vr
    @31
    @11
    @26
    vr
    @31
    wrex
    #
    @34
    @19
    @2
    @5
    @37
    vr
    cP
    cQ
    @30
    @12
    @20
    cK
    cN
    @24
    vq
    psgndif.p
    @20
    eqid
    #
    @12
    eqid
    #
    @24
    eqid
    #
    @30
    eqid
    #
    psgnfix2
    imp
    ad2antrr
    @36
    @26
    @28
    wi
    vr
    @31
    @36
    @25
    @31
    wcel
    #
    wa
    @26
    @17
    @27
    wceq
    #
    @28
    @35
    @14
    @42
    @26
    @43
    wi
    #
    @18
    @11
    @34
    @14
    @42
    @44
    @11
    @34
    @14
    @42
    w3a
    #
    @44
    cP
    cQ
    @30
    @12
    @20
    @25
    cK
    cN
    @13
    @24
    vq
    psgndif.p
    @38
    @39
    @40
    @41
    psgndiflemA
    #
    imp
    3anassrs
    adantlrr
    @36
    @28
    @43
    wb
    #
    @42
    @18
    @47
    @35
    @14
    @15
    @17
    @27
    eqeq1
    ad2antll
    adantr
    sylibrd
    ralrimiva
    r19.29imd
    ex
    rexlimdva
    @11
    @29
    @22
    vr
    @31
    @11
    @42
    wa
    #
    @29
    @22
    @48
    @29
    wa
    #
    @14
    @18
    vw
    @21
    @11
    @14
    vw
    @21
    wrex
    #
    @42
    @29
    @2
    @5
    @50
    vw
    cP
    cQ
    @12
    @20
    cK
    cN
    vq
    psgndif.p
    @38
    @39
    psgnfix1
    imp
    ad2antrr
    @49
    @14
    @18
    wi
    vw
    @21
    @49
    @34
    wa
    @14
    @27
    @17
    wceq
    #
    @18
    @48
    @26
    @34
    @14
    @51
    wi
    @28
    @48
    @26
    wa
    #
    @34
    wa
    #
    @14
    @51
    @53
    @14
    wa
    #
    @17
    @27
    @54
    @11
    @45
    @26
    @43
    @11
    @42
    @26
    @34
    @14
    simp-4l
    @54
    @34
    @14
    @42
    @53
    @34
    @14
    @52
    @34
    simpr
    adantr
    @53
    @14
    simpr
    @11
    @42
    @26
    @34
    @14
    simp-4r
    3jca
    @52
    @26
    @34
    @14
    @48
    @26
    simpr
    ad2antrr
    @46
    syl3c
    eqcomd
    ex
    adantlrr
    @49
    @18
    @51
    wb
    #
    @34
    @28
    @55
    @48
    @26
    @15
    @27
    @17
    eqeq1
    ad2antll
    adantr
    sylibrd
    ralrimiva
    r19.29imd
    ex
    rexlimdva
    impbid
    iotabidv
    @11
    @7
    cfn
    wcel
    #
    @8
    @12
    cbs
    cfv
    #
    wcel
    #
    @9
    @23
    wceq
    @0
    @56
    @1
    @5
    cN
    @6
    diffi
    ad2antrr
    @1
    @5
    @58
    @0
    @7
    cP
    @4
    @57
    cQ
    cK
    cN
    vq
    psgndif.p
    @4
    eqid
    @57
    eqid
    #
    @7
    eqid
    symgfixelsi
    adantll
    vw
    @57
    @7
    @8
    @20
    @12
    cZ
    vs
    @39
    @59
    @38
    psgndif.z
    psgnvalfi
    syl2anc
    @2
    @0
    cQ
    cP
    wcel
    @10
    @33
    wceq
    @5
    @0
    @1
    simpl
    @3
    vq
    cQ
    cP
    elrabi
    vr
    cP
    cN
    cQ
    @30
    @24
    cS
    vs
    @40
    psgndif.p
    @41
    psgndif.s
    psgnvalfi
    syl2an
    3eqtr4d
    ex
end
