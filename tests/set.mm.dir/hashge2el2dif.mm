include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wral.mm"
include "wn.mm"
include "cv.mm"
include "wne.mm"
include "wrex.mm"
include "csn.mm"
include "wceq.mm"
include "wi.mm"
include "c1.mm"
include "fveq2.mm"
include "hashsng.mm"
include "sylan9eqr.mm"
include "ralimiaa.mm"
include "c0.mm"
include "cc0.mm"
include "clt.mm"
include "cfn.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "w3a.mm"
include "0re.mm"
include "1re.mm"
include "readdcli.mm"
include "a1i.mm"
include "2re.mm"
include "hashcl.mm"
include "nn0red.mm"
include "adantr.mm"
include "3jca.mm"
include "0p1e1.mm"
include "1lt2.mm"
include "eqbrtri.mm"
include "jctl.mm"
include "adantl.mm"
include "ltleletr.mm"
include "sylc.mm"
include "cz.mm"
include "wb.mm"
include "nn0zd.mm"
include "0z.mm"
include "jctil.mm"
include "zltp1le.mm"
include "syl.mm"
include "mpbird.mm"
include "cpnf.mm"
include "0ltpnf.mm"
include "simpl.mm"
include "anim2i.mm"
include "ancomd.mm"
include "hashinf.mm"
include "syl5breqr.mm"
include "pm2.61ian.mm"
include "hashgt0n0.mm"
include "syldan.mm"
include "rspn0.mm"
include "breq2.mm"
include "ltnlei.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "com12.mm"
include "syldc.mm"
include "ax-1.mm"
include "pm2.61i.mm"
include "eqsn.mm"
include "equcom.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "mtbid.mm"
include "df-ne.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "sylibr.mm"

theorem hashge2el2dif
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cV: class V

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint V x
  disjoint V y
  assert |- ( ( D e. V /\ 2 <_ ( # ` D ) ) -> E. x e. D E. y e. D x =/= y )

  proof
    cD
    cV
    wcel
    #
    c2
    cD
    chash
    cfv
    #
    cle
    wbr
    #
    wa
    #
    vx
    vy
    weq
    #
    vy
    cD
    wral
    #
    vx
    cD
    wral
    #
    wn
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    vy
    cD
    wrex
    #
    vx
    cD
    wrex
    #
    @3
    cD
    @8
    csn
    #
    wceq
    #
    vx
    cD
    wral
    #
    @6
    @15
    @3
    @15
    wn
    #
    wi
    #
    @15
    @1
    c1
    wceq
    #
    vx
    cD
    wral
    #
    @17
    @14
    @18
    vx
    cD
    @14
    @8
    cD
    wcel
    @1
    @13
    chash
    cfv
    c1
    cD
    @13
    chash
    fveq2
    @8
    cD
    hashsng
    sylan9eqr
    ralimiaa
    @3
    @19
    @18
    @16
    @3
    cD
    c0
    wne
    #
    @19
    @18
    wi
    @0
    @2
    cc0
    @1
    clt
    wbr
    #
    @20
    cD
    cfn
    wcel
    #
    @3
    @21
    @22
    @3
    wa
    #
    @21
    cc0
    c1
    caddc
    co
    #
    @1
    cle
    wbr
    #
    @23
    @24
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    w3a
    @24
    c2
    clt
    wbr
    #
    @2
    wa
    #
    @25
    @23
    @26
    @27
    @28
    @26
    @23
    cc0
    c1
    0re
    1re
    readdcli
    a1i
    @27
    @23
    2re
    a1i
    @22
    @28
    @3
    @22
    @1
    cD
    hashcl
    #
    nn0red
    adantr
    3jca
    @3
    @30
    @22
    @2
    @30
    @0
    @2
    @29
    @24
    c1
    c2
    clt
    0p1e1
    1lt2
    eqbrtri
    jctl
    adantl
    adantl
    @24
    c2
    @1
    ltleletr
    sylc
    @23
    cc0
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    wa
    #
    @21
    @25
    wb
    @22
    @34
    @3
    @22
    @33
    @32
    @22
    @1
    @31
    nn0zd
    0z
    jctil
    adantr
    cc0
    @1
    zltp1le
    syl
    mpbird
    @22
    wn
    #
    @3
    wa
    #
    cc0
    cpnf
    @1
    clt
    0ltpnf
    @36
    @0
    @35
    wa
    @1
    cpnf
    wceq
    @36
    @35
    @0
    @3
    @0
    @35
    @0
    @2
    simpl
    anim2i
    ancomd
    cD
    cV
    hashinf
    syl
    syl5breqr
    pm2.61ian
    cD
    cV
    hashgt0n0
    syldan
    #
    @18
    vx
    cD
    rspn0
    syl
    @2
    @18
    @16
    wi
    @0
    @18
    @2
    @16
    @18
    @2
    c2
    c1
    cle
    wbr
    #
    @16
    @1
    c1
    c2
    cle
    breq2
    c1
    c2
    clt
    wbr
    #
    @38
    @16
    wi
    #
    1lt2
    @39
    @38
    wn
    @40
    c1
    c2
    1re
    2re
    ltnlei
    @38
    @16
    pm2.21
    sylbi
    ax-mp
    syl6bi
    com12
    adantl
    syldc
    syl
    @16
    @3
    ax-1
    pm2.61i
    @3
    @14
    @5
    vx
    cD
    @3
    @14
    vy
    vx
    weq
    #
    vy
    cD
    wral
    #
    @5
    @3
    @20
    @14
    @42
    wb
    @37
    vy
    cD
    @8
    eqsn
    syl
    @3
    @41
    @4
    vy
    cD
    @41
    @4
    wb
    @3
    vy
    vx
    equcom
    a1i
    ralbidv
    bitrd
    ralbidv
    mtbid
    @12
    @5
    wn
    #
    vx
    cD
    wrex
    @7
    @11
    @43
    vx
    cD
    @11
    @4
    wn
    #
    vy
    cD
    wrex
    @43
    @10
    @44
    vy
    cD
    @8
    @9
    df-ne
    rexbii
    @4
    vy
    cD
    rexnal
    bitri
    rexbii
    @5
    vx
    cD
    rexnal
    bitri
    sylibr
end
