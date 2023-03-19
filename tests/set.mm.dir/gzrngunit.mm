include "cui.mm"
include "cfv.mm"
include "wcel.mm"
include "cgz.mm"
include "cabs.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cbs.mm"
include "gzsubrg.mm"
include "subrgbas.mm"
include "ax-mp.mm"
include "eqid.mm"
include "unitcl.mm"
include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "cinvr.mm"
include "subrginv.mm"
include "mpan.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "gzcn.mm"
include "syl.mm"
include "0red.mm"
include "cr.mm"
include "1re.mm"
include "a1i.mm"
include "abscld.mm"
include "clt.mm"
include "0lt1.mm"
include "gzrngunitlem.mm"
include "ltletrd.mm"
include "gt0ne0d.mm"
include "abs00ad.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "cnfldinv.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "crg.mm"
include "subrgring.mm"
include "unitinvcl.mm"
include "eqeltrrd.mm"
include "1cnd.mm"
include "absdivd.mm"
include "breqtrd.mm"
include "1div1e1.mm"
include "abs1.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "3brtr4g.mm"
include "wb.mm"
include "lerec.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "jca.mm"
include "csn.mm"
include "cdif.mm"
include "adantr.mm"
include "simpr.mm"
include "ax-1ne0.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simpl.mm"
include "ccj.mm"
include "cmul.mm"
include "c2.mm"
include "cexp.mm"
include "absvalsqd.mm"
include "oveq1d.mm"
include "sq1.mm"
include "cjcld.mm"
include "divcan3d.mm"
include "3eqtr2d.mm"
include "gzcjcl.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "subrgunit.mm"
include "syl3anbrc.mm"
include "impbii.mm"

theorem gzrngunit
  let cA: class A
  let cZ: class Z
  assume gzrng.1: |- Z = ( CCfld |`s Z[i] )


  assert |- ( A e. ( Unit ` Z ) <-> ( A e. Z[i] /\ ( abs ` A ) = 1 ) )

  proof
    cA
    cZ
    cui
    cfv
    #
    wcel
    #
    cA
    cgz
    wcel
    #
    cA
    cabs
    cfv
    #
    c1
    wceq
    #
    wa
    #
    @1
    @2
    @4
    cgz
    cZ
    @0
    cA
    cgz
    ccnfld
    csubrg
    cfv
    wcel
    #
    cgz
    cZ
    cbs
    cfv
    wceq
    gzsubrg
    cgz
    ccnfld
    cZ
    gzrng.1
    subrgbas
    ax-mp
    @0
    eqid
    #
    unitcl
    #
    @1
    @4
    @3
    c1
    cle
    wbr
    #
    c1
    @3
    cle
    wbr
    #
    @1
    @9
    c1
    c1
    cdiv
    co
    #
    c1
    @3
    cdiv
    co
    #
    cle
    wbr
    #
    @1
    c1
    c1
    cabs
    cfv
    #
    @3
    cdiv
    co
    #
    @11
    @12
    cle
    @1
    c1
    c1
    cA
    cdiv
    co
    #
    cabs
    cfv
    #
    @15
    cle
    @1
    @16
    @0
    wcel
    c1
    @17
    cle
    wbr
    @1
    cA
    cZ
    cinvr
    cfv
    #
    cfv
    #
    @16
    @0
    @1
    cA
    ccnfld
    cinvr
    cfv
    #
    cfv
    #
    @19
    @16
    @6
    @1
    @21
    @19
    wceq
    gzsubrg
    cgz
    ccnfld
    cZ
    @0
    @20
    @18
    cA
    gzrng.1
    @20
    eqid
    #
    @7
    @18
    eqid
    #
    subrginv
    mpan
    @1
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    @21
    @16
    wceq
    #
    @1
    @2
    @24
    @8
    cA
    gzcn
    #
    syl
    #
    @1
    @3
    cc0
    wne
    #
    @25
    @1
    @3
    @1
    cc0
    c1
    @3
    @1
    0red
    c1
    cr
    wcel
    #
    @1
    1re
    a1i
    #
    @1
    cA
    @28
    abscld
    #
    cc0
    c1
    clt
    wbr
    #
    @1
    0lt1
    a1i
    #
    cA
    cZ
    gzrng.1
    gzrngunitlem
    #
    ltletrd
    #
    gt0ne0d
    @1
    @3
    cc0
    cA
    cc0
    @1
    cA
    @28
    abs00ad
    necon3bid
    mpbid
    #
    cA
    cnfldinv
    #
    syl2anc
    eqtr3d
    cZ
    crg
    wcel
    #
    @1
    @19
    @0
    wcel
    @6
    @39
    gzsubrg
    cgz
    ccnfld
    cZ
    gzrng.1
    subrgring
    ax-mp
    cZ
    @0
    @18
    cA
    @7
    @23
    unitinvcl
    mpan
    eqeltrrd
    @16
    cZ
    gzrng.1
    gzrngunitlem
    syl
    @1
    c1
    cA
    @1
    1cnd
    @28
    @37
    absdivd
    breqtrd
    1div1e1
    c1
    @14
    @3
    cdiv
    @14
    c1
    abs1
    eqcomi
    oveq1i
    3brtr4g
    @1
    @3
    cr
    wcel
    #
    cc0
    @3
    clt
    wbr
    @30
    @33
    @9
    @13
    wb
    @32
    @36
    @31
    @34
    @3
    c1
    lerec
    syl22anc
    mpbird
    @35
    @1
    @40
    @30
    @4
    @9
    @10
    wa
    wb
    @32
    1re
    @3
    c1
    letri3
    sylancl
    mpbir2and
    jca
    @5
    cA
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    @2
    @21
    cgz
    wcel
    #
    @1
    @5
    @24
    @25
    @42
    @2
    @24
    @4
    @27
    adantr
    #
    @5
    @29
    @25
    @5
    @3
    c1
    cc0
    @2
    @4
    simpr
    #
    c1
    cc0
    wne
    @5
    ax-1ne0
    a1i
    eqnetrd
    cA
    cc0
    @3
    cc0
    cA
    cc0
    wceq
    @3
    cc0
    cabs
    cfv
    cc0
    cA
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    necon3i
    syl
    #
    cA
    cc
    cc0
    eldifsn
    sylanbrc
    @2
    @4
    simpl
    @5
    @21
    cA
    ccj
    cfv
    #
    cgz
    @5
    @21
    @16
    cA
    @47
    cmul
    co
    #
    cA
    cdiv
    co
    @47
    @5
    @24
    @25
    @26
    @44
    @46
    @38
    syl2anc
    @5
    @48
    c1
    cA
    cdiv
    @5
    @3
    c2
    cexp
    co
    #
    @48
    c1
    @5
    cA
    @44
    absvalsqd
    @5
    @49
    c1
    c2
    cexp
    co
    c1
    @5
    @3
    c1
    c2
    cexp
    @45
    oveq1d
    sq1
    syl6eq
    eqtr3d
    oveq1d
    @5
    @47
    cA
    @5
    cA
    @44
    cjcld
    @44
    @46
    divcan3d
    3eqtr2d
    @2
    @47
    cgz
    wcel
    @4
    cA
    gzcjcl
    adantr
    eqeltrd
    @6
    @1
    @42
    @2
    @43
    w3a
    wb
    gzsubrg
    cgz
    ccnfld
    cZ
    @41
    @20
    @0
    cA
    gzrng.1
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    @7
    @22
    subrgunit
    ax-mp
    syl3anbrc
    impbii
end
