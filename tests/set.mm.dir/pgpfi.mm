include "cgrp.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cpgp.mm"
include "wbr.mm"
include "cprime.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "cod.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "ispgp.mm"
include "simprl.mm"
include "cdvds.mm"
include "cpc.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "ad2antrr.mm"
include "wb.mm"
include "hashnncl.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "pccld.mm"
include "cle.mm"
include "nn0red.mm"
include "leidd.mm"
include "cz.mm"
include "nn0zd.mm"
include "pcid.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "simpr.mm"
include "oveq1d.mm"
include "3brtr4d.mm"
include "cc0.mm"
include "wn.mm"
include "simp-4l.mm"
include "simplr.mm"
include "odcau.mm"
include "syl31anc.mm"
include "adantr.mm"
include "prmz.mm"
include "iddvds.mm"
include "3syl.mm"
include "simprr.mm"
include "simplrr.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "sylan.mm"
include "ad2ant2r.mm"
include "ad3antrrr.mm"
include "prmnn.mm"
include "syl.mm"
include "eqeltrd.mm"
include "pcprmpw.mm"
include "mpbid.mm"
include "breqtrd.mm"
include "wi.mm"
include "prmdvdsexpr.mm"
include "syl3anc.mm"
include "mpd.mm"
include "rexlimddv.mm"
include "ex.mm"
include "necon3ad.mm"
include "imp.mm"
include "pceq0.mm"
include "ad2antrl.mm"
include "nnexpcld.mm"
include "nn0ge0d.mm"
include "eqbrtrd.mm"
include "pm2.61dane.mm"
include "ralrimiva.mm"
include "hashcl.mm"
include "nnzd.mm"
include "pc2dvds.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rspcev.mm"
include "pcprmpw2.mm"
include "bitr4d.mm"
include "jca.mm"
include "3adantr2.mm"
include "syl5bi.mm"
include "pgpfi1.mm"
include "3expia.mm"
include "rexlimdv.mm"
include "expimpd.mm"
include "impbid.mm"

theorem pgpfi
  let cP: class P
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vg: setvar g
  let vm: setvar m
  let vp: setvar p
  let vx: setvar x
  assume pgpfi.1: |- X = ( Base ` G )

  disjoint G n
  disjoint P n
  disjoint X n
  disjoint g m
  disjoint g n
  disjoint g p
  disjoint g x
  disjoint G g
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint G m
  disjoint n p
  disjoint n x
  disjoint p x
  disjoint G p
  disjoint G x
  disjoint P g
  disjoint P m
  disjoint P p
  disjoint P x
  disjoint X g
  disjoint X p
  disjoint X x
  assert |- ( ( G e. Grp /\ X e. Fin ) -> ( P pGrp G <-> ( P e. Prime /\ E. n e. NN0 ( # ` X ) = ( P ^ n ) ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cfn
    wcel
    #
    wa
    #
    cP
    cG
    cpgp
    wbr
    #
    cP
    cprime
    wcel
    #
    cX
    chash
    cfv
    #
    cP
    vn
    cv
    #
    cexp
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    #
    wa
    #
    @3
    @4
    @0
    vx
    cv
    #
    cG
    cod
    cfv
    #
    cfv
    #
    cP
    vm
    cv
    cexp
    co
    #
    wceq
    #
    vm
    cn0
    wrex
    #
    vx
    cX
    wral
    #
    w3a
    #
    @2
    @10
    vx
    cP
    vm
    cG
    @12
    cX
    pgpfi.1
    @12
    eqid
    #
    ispgp
    @2
    @18
    @10
    @2
    @4
    @17
    @10
    @0
    @2
    @4
    @17
    wa
    #
    wa
    #
    @4
    @9
    @2
    @4
    @17
    simprl
    #
    @21
    @5
    @7
    cdvds
    wbr
    #
    vn
    cn0
    wrex
    #
    @9
    @21
    cP
    @5
    cpc
    co
    #
    cn0
    wcel
    @5
    cP
    @25
    cexp
    co
    #
    cdvds
    wbr
    #
    @24
    @21
    cP
    @5
    @22
    @21
    @5
    cn
    wcel
    #
    cX
    c0
    wne
    #
    @0
    @29
    @1
    @20
    cX
    cG
    pgpfi.1
    grpbn0
    ad2antrr
    @1
    @28
    @29
    wb
    @0
    @20
    cX
    hashnncl
    ad2antlr
    mpbird
    #
    pccld
    #
    @21
    @27
    vp
    cv
    #
    @5
    cpc
    co
    #
    @32
    @26
    cpc
    co
    #
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @21
    @35
    vp
    cprime
    @21
    @32
    cprime
    wcel
    #
    wa
    #
    @35
    @32
    cP
    @38
    @32
    cP
    wceq
    #
    wa
    #
    @25
    cP
    @26
    cpc
    co
    #
    @33
    @34
    cle
    @21
    @25
    @41
    cle
    wbr
    @37
    @39
    @21
    @25
    @25
    @41
    cle
    @21
    @25
    @21
    @25
    @31
    nn0red
    leidd
    @21
    @4
    @25
    cz
    wcel
    @41
    @25
    wceq
    @22
    @21
    @25
    @31
    nn0zd
    @25
    cP
    pcid
    syl2anc
    breqtrrd
    ad2antrr
    @40
    @32
    cP
    @5
    cpc
    @38
    @39
    simpr
    #
    oveq1d
    @40
    @32
    cP
    @26
    cpc
    @42
    oveq1d
    3brtr4d
    @38
    @32
    cP
    wne
    #
    wa
    #
    @33
    cc0
    @34
    cle
    @44
    @33
    cc0
    wceq
    #
    @32
    @5
    cdvds
    wbr
    #
    wn
    #
    @38
    @43
    @47
    @38
    @46
    @32
    cP
    @38
    @46
    @39
    @38
    @46
    wa
    #
    vg
    cv
    #
    @12
    cfv
    #
    @32
    wceq
    #
    @39
    vg
    cX
    @48
    @0
    @1
    @37
    @46
    @51
    vg
    cX
    wrex
    @0
    @1
    @20
    @37
    @46
    simp-4l
    @21
    @1
    @37
    @46
    @0
    @1
    @20
    simplr
    ad2antrr
    @21
    @37
    @46
    simplr
    #
    @38
    @46
    simpr
    @32
    vg
    cG
    @12
    cX
    pgpfi.1
    @19
    odcau
    syl31anc
    @48
    @49
    cX
    wcel
    #
    @51
    wa
    #
    wa
    #
    @32
    cP
    cP
    @50
    cpc
    co
    #
    cexp
    co
    #
    cdvds
    wbr
    #
    @39
    @55
    @32
    @50
    @57
    cdvds
    @55
    @32
    @32
    @50
    cdvds
    @55
    @37
    @32
    cz
    wcel
    @32
    @32
    cdvds
    wbr
    @48
    @37
    @54
    @52
    adantr
    #
    @32
    prmz
    @32
    iddvds
    3syl
    @48
    @53
    @51
    simprr
    #
    breqtrrd
    @55
    @50
    @14
    wceq
    #
    vm
    cn0
    wrex
    #
    @50
    @57
    wceq
    #
    @38
    @53
    @62
    @46
    @51
    @38
    @17
    @53
    @62
    @2
    @4
    @17
    @37
    simplrr
    @16
    @62
    vx
    @49
    cX
    @11
    @49
    wceq
    #
    @15
    @61
    vm
    cn0
    @64
    @13
    @50
    @14
    @11
    @49
    @12
    fveq2
    eqeq1d
    rexbidv
    rspccva
    sylan
    ad2ant2r
    @55
    @4
    @50
    cn
    wcel
    @62
    @63
    wb
    @21
    @4
    @37
    @46
    @54
    @22
    ad3antrrr
    #
    @55
    @50
    @32
    cn
    @60
    @55
    @37
    @32
    cn
    wcel
    @59
    @32
    prmnn
    syl
    eqeltrd
    #
    @50
    cP
    vm
    pcprmpw
    syl2anc
    mpbid
    breqtrd
    @55
    @37
    @4
    @56
    cn0
    wcel
    @58
    @39
    wi
    @59
    @65
    @55
    cP
    @50
    @65
    @66
    pccld
    @32
    cP
    @56
    prmdvdsexpr
    syl3anc
    mpd
    rexlimddv
    ex
    necon3ad
    imp
    @44
    @37
    @28
    @45
    @47
    wb
    @21
    @37
    @43
    simplr
    #
    @21
    @28
    @37
    @43
    @30
    ad2antrr
    @32
    @5
    pceq0
    syl2anc
    mpbird
    @44
    @34
    @44
    @32
    @26
    @67
    @21
    @26
    cn
    wcel
    @37
    @43
    @21
    cP
    @25
    @4
    cP
    cn
    wcel
    @2
    @17
    cP
    prmnn
    ad2antrl
    @31
    nnexpcld
    #
    ad2antrr
    pccld
    nn0ge0d
    eqbrtrd
    pm2.61dane
    ralrimiva
    @21
    @5
    cz
    wcel
    @26
    cz
    wcel
    @27
    @36
    wb
    @21
    @5
    @1
    @5
    cn0
    wcel
    @0
    @20
    cX
    hashcl
    ad2antlr
    nn0zd
    @21
    @26
    @68
    nnzd
    @5
    @26
    vp
    pc2dvds
    syl2anc
    mpbird
    @23
    @27
    vn
    @25
    cn0
    @6
    @25
    wceq
    @7
    @26
    @5
    cdvds
    @6
    @25
    cP
    cexp
    oveq2
    breq2d
    rspcev
    syl2anc
    @21
    @4
    @28
    @24
    @9
    wb
    @22
    @30
    @4
    @28
    wa
    @24
    @5
    @26
    wceq
    @9
    @5
    cP
    vn
    pcprmpw2
    @5
    cP
    vn
    pcprmpw
    bitr4d
    syl2anc
    mpbid
    jca
    3adantr2
    ex
    syl5bi
    @0
    @10
    @3
    wi
    @1
    @0
    @4
    @9
    @3
    @0
    @4
    wa
    @8
    @3
    vn
    cn0
    @0
    @4
    @6
    cn0
    wcel
    @8
    @3
    wi
    cP
    cG
    @6
    cX
    pgpfi.1
    pgpfi1
    3expia
    rexlimdv
    expimpd
    adantr
    impbid
end
