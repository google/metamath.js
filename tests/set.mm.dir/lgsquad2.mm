include "cv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cgcd.mm"
include "c1.mm"
include "wceq.mm"
include "clgs.mm"
include "cneg.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "wi.mm"
include "cfz.mm"
include "wral.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "adantr.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "simprl.mm"
include "eldifi.mm"
include "syl.mm"
include "prmnn.mm"
include "wne.mm"
include "eldifsni.mm"
include "necomd.mm"
include "neneqd.mm"
include "cuz.mm"
include "cfv.mm"
include "wb.mm"
include "cz.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "dvdsprm.mm"
include "sylancr.mm"
include "mtbird.mm"
include "nnzd.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "simprr.mm"
include "eqtrd.mm"
include "prmrp.mm"
include "syl2anr.mm"
include "biimpd.mm"
include "impr.mm"
include "lgsquad.mm"
include "syl3anc.mm"
include "biid.mm"
include "lgsquad2lem2.mm"
include "lgscl.mm"
include "cc.mm"
include "zcn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "nncnd.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancl.mm"
include "halfcld.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem lgsquad2
  let wph: wff ph
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume lgsquad2.1: |- ( ph -> M e. NN )
  assume lgsquad2.2: |- ( ph -> -. 2 || M )
  assume lgsquad2.3: |- ( ph -> N e. NN )
  assume lgsquad2.4: |- ( ph -> -. 2 || N )
  assume lgsquad2.5: |- ( ph -> ( M gcd N ) = 1 )


  assert |- ( ph -> ( ( M /L N ) x. ( N /L M ) ) = ( -u 1 ^ ( ( ( M - 1 ) / 2 ) x. ( ( N - 1 ) / 2 ) ) ) )

  proof
    wph
    vx
    cv
    #
    c2
    cN
    cmul
    co
    cgcd
    co
    c1
    wceq
    @0
    cN
    clgs
    co
    cN
    @0
    clgs
    co
    cmul
    co
    c1
    cneg
    #
    @0
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    cexp
    co
    wceq
    wi
    vx
    c1
    vy
    cv
    cfz
    co
    #
    wral
    #
    vx
    vy
    vm
    cM
    cN
    lgsquad2.1
    lgsquad2.2
    lgsquad2.3
    lgsquad2.4
    lgsquad2.5
    wph
    vm
    cv
    #
    cprime
    c2
    csn
    #
    cdif
    #
    wcel
    #
    @7
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    wa
    #
    wa
    #
    cN
    @7
    clgs
    co
    #
    @7
    cN
    clgs
    co
    #
    cmul
    co
    #
    @1
    @4
    @7
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cmul
    co
    #
    cexp
    co
    @16
    @15
    cmul
    co
    #
    @1
    @19
    @4
    cmul
    co
    #
    cexp
    co
    @14
    @0
    c2
    @7
    cmul
    co
    cgcd
    co
    c1
    wceq
    @0
    @7
    clgs
    co
    @7
    @0
    clgs
    co
    cmul
    co
    @1
    @2
    @19
    cmul
    co
    cexp
    co
    wceq
    wi
    vx
    @5
    wral
    #
    vx
    vy
    vn
    cN
    @7
    wph
    cN
    cn
    wcel
    @13
    lgsquad2.3
    adantr
    #
    wph
    c2
    cN
    cdvds
    wbr
    wn
    @13
    lgsquad2.4
    adantr
    @14
    @7
    cprime
    wcel
    #
    @7
    cn
    wcel
    @14
    @10
    @25
    wph
    @10
    @12
    simprl
    #
    @7
    cprime
    @8
    eldifi
    syl
    #
    @7
    prmnn
    syl
    #
    @14
    c2
    @7
    cdvds
    wbr
    #
    c2
    @7
    wceq
    #
    @14
    c2
    @7
    @14
    @7
    c2
    @14
    @10
    @7
    c2
    wne
    @26
    @7
    cprime
    c2
    eldifsni
    syl
    necomd
    neneqd
    @14
    c2
    c2
    cuz
    cfv
    wcel
    #
    @25
    @29
    @30
    wb
    c2
    cz
    wcel
    @31
    2z
    c2
    uzid
    ax-mp
    @27
    @7
    c2
    dvdsprm
    sylancr
    mtbird
    @14
    cN
    @7
    cgcd
    co
    #
    @11
    c1
    @14
    cN
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @32
    @11
    wceq
    @14
    cN
    @24
    nnzd
    #
    @14
    @7
    @28
    nnzd
    #
    cN
    @7
    gcdcom
    syl2anc
    wph
    @10
    @12
    simprr
    eqtrd
    @14
    vn
    cv
    #
    @9
    wcel
    #
    @37
    @7
    cgcd
    co
    c1
    wceq
    #
    wa
    #
    wa
    @38
    @10
    @37
    @7
    wne
    #
    @37
    @7
    clgs
    co
    @7
    @37
    clgs
    co
    cmul
    co
    @1
    @37
    c1
    cmin
    co
    c2
    cdiv
    co
    @19
    cmul
    co
    cexp
    co
    wceq
    @14
    @38
    @39
    simprl
    @14
    @10
    @40
    @26
    adantr
    @14
    @38
    @39
    @41
    @14
    @38
    wa
    @39
    @41
    @38
    @37
    cprime
    wcel
    @25
    @39
    @41
    wb
    @14
    @37
    cprime
    @8
    eldifi
    @27
    @37
    @7
    prmrp
    syl2anr
    biimpd
    impr
    @37
    @7
    lgsquad
    syl3anc
    @23
    biid
    lgsquad2lem2
    @14
    @16
    cz
    wcel
    #
    @15
    cz
    wcel
    #
    @21
    @17
    wceq
    #
    @14
    @34
    @33
    @42
    @36
    @35
    @7
    cN
    lgscl
    syl2anc
    @14
    @33
    @34
    @43
    @35
    @36
    cN
    @7
    lgscl
    syl2anc
    @42
    @16
    cc
    wcel
    @15
    cc
    wcel
    @44
    @43
    @16
    zcn
    @15
    zcn
    @16
    @15
    mulcom
    syl2an
    syl2anc
    @14
    @22
    @20
    @1
    cexp
    @14
    @19
    @4
    @14
    @18
    @14
    @7
    cc
    wcel
    c1
    cc
    wcel
    #
    @18
    cc
    wcel
    @14
    @7
    @28
    nncnd
    ax-1cn
    @7
    c1
    subcl
    sylancl
    halfcld
    @14
    @3
    @14
    cN
    cc
    wcel
    @45
    @3
    cc
    wcel
    @14
    cN
    @24
    nncnd
    ax-1cn
    cN
    c1
    subcl
    sylancl
    halfcld
    mulcomd
    oveq2d
    3eqtr4d
    @6
    biid
    lgsquad2lem2
end
