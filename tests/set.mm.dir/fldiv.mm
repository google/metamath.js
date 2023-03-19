include "cr.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "caddc.mm"
include "wceq.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "clt.mm"
include "eqid.mm"
include "intfrac2.mm"
include "simp3d.mm"
include "adantr.mm"
include "oveq1d.mm"
include "cc.mm"
include "wne.mm"
include "reflcl.mm"
include "recnd.mm"
include "resubcl.mm"
include "mpdan.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "adantl.mm"
include "divdir.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "cz.mm"
include "flcl.mm"
include "intfracq.mm"
include "sylan.mm"
include "nnre.mm"
include "redivcld.mm"
include "syl.mm"
include "resubcld.mm"
include "addassd.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "simp1d.mm"
include "fracge0.mm"
include "nngt0.mm"
include "divge0.mm"
include "syl2an.mm"
include "addge0d.mm"
include "peano2rem.mm"
include "nnrecre.mm"
include "jca31.mm"
include "simp2d.mm"
include "fraclt1.mm"
include "wb.mm"
include "1re.mm"
include "ltdiv1.mm"
include "mp3an2.mm"
include "mpbid.mm"
include "leltadd.mm"
include "sylc.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "syl12anc.mm"
include "dividd.mm"
include "3eqtr3d.mm"
include "breqtrd.mm"
include "flcld.mm"
include "readdcld.mm"
include "flbi2.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "eqtr2d.mm"

theorem fldiv
  let cA: class A
  let cN: class N


  assert |- ( ( A e. RR /\ N e. NN ) -> ( |_ ` ( ( |_ ` A ) / N ) ) = ( |_ ` ( A / N ) ) )

  proof
    cA
    cr
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cA
    cN
    cdiv
    co
    #
    cfl
    cfv
    cA
    cfl
    cfv
    #
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    @5
    @6
    cmin
    co
    #
    cA
    @4
    cmin
    co
    #
    cN
    cdiv
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @6
    @2
    @3
    @11
    cfl
    @2
    @3
    @5
    @9
    caddc
    co
    #
    @6
    @7
    caddc
    co
    #
    @9
    caddc
    co
    @11
    @2
    @3
    @4
    @8
    caddc
    co
    #
    cN
    cdiv
    co
    #
    @13
    @2
    cA
    @15
    cN
    cdiv
    @0
    cA
    @15
    wceq
    #
    @1
    @0
    cc0
    @8
    cle
    wbr
    #
    @8
    c1
    clt
    wbr
    #
    @17
    cA
    @8
    @4
    @4
    eqid
    @8
    eqid
    intfrac2
    simp3d
    adantr
    oveq1d
    @2
    @4
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    #
    @16
    @13
    wceq
    @0
    @20
    @1
    @0
    @4
    cA
    reflcl
    #
    recnd
    adantr
    @0
    @21
    @1
    @0
    @8
    @0
    @4
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @25
    cA
    @4
    resubcl
    mpdan
    #
    recnd
    adantr
    @1
    @24
    @0
    @1
    @22
    @23
    cN
    nncn
    #
    cN
    nnne0
    #
    jca
    adantl
    @4
    @8
    cN
    divdir
    syl3anc
    eqtrd
    @2
    @5
    @14
    @9
    caddc
    @0
    @4
    cz
    wcel
    #
    @1
    @5
    @14
    wceq
    #
    cA
    flcl
    #
    @31
    @1
    wa
    #
    cc0
    @7
    cle
    wbr
    #
    @7
    cN
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    #
    cle
    wbr
    #
    @32
    @7
    @4
    cN
    @6
    @6
    eqid
    @7
    eqid
    intfracq
    #
    simp3d
    sylan
    oveq1d
    @2
    @6
    @7
    @9
    @2
    @6
    @2
    @5
    cr
    wcel
    @6
    cr
    wcel
    @2
    @4
    cN
    @0
    @26
    @1
    @25
    adantr
    @1
    cN
    cr
    wcel
    #
    @0
    cN
    nnre
    #
    adantl
    #
    @1
    @23
    @0
    @30
    adantl
    #
    redivcld
    #
    @5
    reflcl
    syl
    #
    recnd
    @2
    @7
    @2
    @5
    @6
    @44
    @45
    resubcld
    #
    recnd
    @2
    @9
    @2
    @8
    cN
    @0
    @27
    @1
    @28
    adantr
    @42
    @43
    redivcld
    #
    recnd
    addassd
    3eqtrd
    fveq2d
    @2
    @12
    @6
    wceq
    #
    cc0
    @10
    cle
    wbr
    #
    @10
    c1
    clt
    wbr
    #
    @2
    @7
    @9
    @46
    @47
    @0
    @31
    @1
    @35
    @33
    @34
    @35
    @38
    @32
    @39
    simp1d
    sylan
    @0
    @27
    @18
    wa
    @40
    cc0
    cN
    clt
    wbr
    #
    wa
    #
    cc0
    @9
    cle
    wbr
    @1
    @0
    @27
    @18
    @28
    cA
    fracge0
    jca
    @1
    @40
    @51
    @41
    cN
    nngt0
    jca
    #
    @8
    cN
    divge0
    syl2an
    addge0d
    @2
    @10
    @37
    c1
    cN
    cdiv
    co
    #
    caddc
    co
    #
    c1
    clt
    @2
    @7
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    wa
    @37
    cr
    wcel
    #
    @54
    cr
    wcel
    #
    wa
    #
    wa
    @38
    @9
    @54
    clt
    wbr
    #
    wa
    @10
    @55
    clt
    wbr
    @2
    @56
    @57
    @60
    @46
    @47
    @1
    @60
    @0
    @1
    @58
    @59
    @1
    @36
    cN
    @1
    @40
    @36
    cr
    wcel
    @41
    cN
    peano2rem
    syl
    #
    @41
    @30
    redivcld
    cN
    nnrecre
    jca
    adantl
    jca31
    @2
    @38
    @61
    @0
    @31
    @1
    @38
    @33
    @34
    @35
    @38
    @32
    @39
    simp2d
    sylan
    @2
    @19
    @61
    @0
    @19
    @1
    cA
    fraclt1
    adantr
    @0
    @27
    @52
    @19
    @61
    wb
    #
    @1
    @28
    @53
    @27
    c1
    cr
    wcel
    @52
    @63
    1re
    @8
    c1
    cN
    ltdiv1
    mp3an2
    syl2an
    mpbid
    jca
    @7
    @9
    @37
    @54
    leltadd
    sylc
    @1
    @55
    c1
    wceq
    @0
    @1
    @36
    c1
    caddc
    co
    #
    cN
    cdiv
    co
    #
    cN
    cN
    cdiv
    co
    @55
    c1
    @1
    @64
    cN
    cN
    cdiv
    @1
    @22
    c1
    cc
    wcel
    #
    @64
    cN
    wceq
    @29
    ax-1cn
    cN
    c1
    npcan
    sylancl
    oveq1d
    @1
    @36
    cc
    wcel
    #
    @22
    @23
    @65
    @55
    wceq
    #
    @1
    @36
    @62
    recnd
    @29
    @30
    @67
    @66
    @24
    @68
    ax-1cn
    @36
    c1
    cN
    divdir
    mp3an2
    syl12anc
    @1
    cN
    @29
    @30
    dividd
    3eqtr3d
    adantl
    breqtrd
    @2
    @6
    cz
    wcel
    @10
    cr
    wcel
    @48
    @49
    @50
    wa
    wb
    @2
    @5
    @44
    flcld
    @2
    @7
    @9
    @46
    @47
    readdcld
    @10
    @6
    flbi2
    syl2anc
    mpbir2and
    eqtr2d
end
