include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "c1.mm"
include "wceq.mm"
include "wrex.mm"
include "clt.mm"
include "wbr.mm"
include "cpell1qr.mm"
include "cfv.mm"
include "csqrt.mm"
include "cq.mm"
include "wn.mm"
include "eldifi.mm"
include "eldifn.mm"
include "wa.mm"
include "anim1i.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "df-squarenn.mm"
include "elrab2.mm"
include "sylibr.mm"
include "mtand.mm"
include "pellex.mm"
include "syl2anc.mm"
include "caddc.mm"
include "cn0.mm"
include "simpll.mm"
include "nnnn0.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "simpr.mm"
include "pellqrexplicit.mm"
include "syl31anc.mm"
include "cr.mm"
include "1re.mm"
include "a1i.mm"
include "readdcli.mm"
include "nnre.mm"
include "ad2antrl.mm"
include "nnrpd.mm"
include "rpsqrtcld.mm"
include "rpred.mm"
include "ad2antll.mm"
include "remulcld.mm"
include "readdcld.mm"
include "ltp1i.mm"
include "cle.mm"
include "nnge1.mm"
include "1t1e1.mm"
include "sq1.mm"
include "nncn.mm"
include "sqsqrtd.mm"
include "3brtr4d.mm"
include "nnrp.mm"
include "cc0.mm"
include "0le1.mm"
include "rpge0d.mm"
include "le2sqd.mm"
include "mpbird.mm"
include "syl.mm"
include "wi.mm"
include "jctir.mm"
include "lemul12a.mm"
include "syl22anc.mm"
include "mp2and.mm"
include "syl5eqbrr.mm"
include "le2addd.mm"
include "ltletrd.mm"
include "breq2.mm"
include "rspcev.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem pellqrex
  let vx: setvar x
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A

  disjoint D x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint A b
  disjoint c d
  disjoint A c
  disjoint A d
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  assert |- ( D e. ( NN \ []NN ) -> E. x e. ( Pell1QR ` D ) 1 < x )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    vc
    cv
    #
    c2
    cexp
    co
    cD
    vd
    cv
    #
    c2
    cexp
    co
    cmul
    co
    cmin
    co
    c1
    wceq
    #
    vd
    cn
    wrex
    vc
    cn
    wrex
    #
    c1
    vx
    cv
    #
    clt
    wbr
    #
    vx
    cD
    cpell1qr
    cfv
    #
    wrex
    #
    @0
    cD
    cn
    wcel
    #
    cD
    csqrt
    cfv
    #
    cq
    wcel
    #
    wn
    @4
    cD
    cn
    csquarenn
    eldifi
    #
    @0
    @11
    cD
    csquarenn
    wcel
    #
    cD
    cn
    csquarenn
    eldifn
    @0
    @11
    wa
    @9
    @11
    wa
    @13
    @0
    @9
    @11
    @12
    anim1i
    va
    cv
    #
    csqrt
    cfv
    #
    cq
    wcel
    @11
    va
    cD
    cn
    csquarenn
    @14
    cD
    wceq
    @15
    @10
    cq
    @14
    cD
    csqrt
    fveq2
    eleq1d
    va
    df-squarenn
    elrab2
    sylibr
    mtand
    vc
    vd
    cD
    pellex
    syl2anc
    @0
    @3
    @8
    vc
    vd
    cn
    cn
    @0
    @1
    cn
    wcel
    #
    @2
    cn
    wcel
    #
    wa
    #
    wa
    #
    @3
    @8
    @19
    @3
    wa
    #
    @1
    @10
    @2
    cmul
    co
    #
    caddc
    co
    #
    @7
    wcel
    #
    c1
    @22
    clt
    wbr
    #
    @8
    @20
    @0
    @1
    cn0
    wcel
    #
    @2
    cn0
    wcel
    #
    @3
    @23
    @0
    @18
    @3
    simpll
    @18
    @25
    @0
    @3
    @16
    @25
    @17
    @1
    nnnn0
    adantr
    ad2antlr
    @18
    @26
    @0
    @3
    @17
    @26
    @16
    @2
    nnnn0
    adantl
    ad2antlr
    @19
    @3
    simpr
    @1
    @2
    cD
    pellqrexplicit
    syl31anc
    @19
    @24
    @3
    @19
    c1
    c1
    c1
    caddc
    co
    #
    @22
    c1
    cr
    wcel
    #
    @19
    1re
    a1i
    #
    @27
    cr
    wcel
    @19
    c1
    c1
    1re
    1re
    readdcli
    a1i
    @19
    @1
    @21
    @16
    @1
    cr
    wcel
    @0
    @17
    @1
    nnre
    ad2antrl
    #
    @19
    @10
    @2
    @19
    @10
    @19
    cD
    @19
    cD
    @0
    @9
    @18
    @12
    adantr
    #
    nnrpd
    rpsqrtcld
    rpred
    #
    @17
    @2
    cr
    wcel
    #
    @0
    @16
    @2
    nnre
    ad2antll
    #
    remulcld
    #
    readdcld
    c1
    @27
    clt
    wbr
    @19
    c1
    1re
    ltp1i
    a1i
    @19
    c1
    c1
    @1
    @21
    @29
    @29
    @30
    @35
    @16
    c1
    @1
    cle
    wbr
    @0
    @17
    @1
    nnge1
    ad2antrl
    @19
    c1
    c1
    c1
    cmul
    co
    #
    @21
    cle
    1t1e1
    @19
    c1
    @10
    cle
    wbr
    #
    c1
    @2
    cle
    wbr
    #
    @36
    @21
    cle
    wbr
    #
    @19
    @9
    @37
    @31
    @9
    @37
    c1
    c2
    cexp
    co
    #
    @10
    c2
    cexp
    co
    #
    cle
    wbr
    @9
    c1
    cD
    @40
    @41
    cle
    cD
    nnge1
    @40
    c1
    wceq
    @9
    sq1
    a1i
    @9
    cD
    cD
    nncn
    sqsqrtd
    3brtr4d
    @9
    c1
    @10
    @28
    @9
    1re
    a1i
    @9
    @10
    @9
    cD
    cD
    nnrp
    rpsqrtcld
    #
    rpred
    cc0
    c1
    cle
    wbr
    #
    @9
    0le1
    a1i
    @9
    @10
    @42
    rpge0d
    le2sqd
    mpbird
    syl
    @17
    @38
    @0
    @16
    @2
    nnge1
    ad2antll
    @19
    @28
    @43
    wa
    #
    @10
    cr
    wcel
    @44
    @33
    @37
    @38
    wa
    @39
    wi
    @19
    @28
    @43
    @29
    0le1
    jctir
    #
    @32
    @45
    @34
    c1
    @10
    c1
    @2
    lemul12a
    syl22anc
    mp2and
    syl5eqbrr
    le2addd
    ltletrd
    adantr
    @6
    @24
    vx
    @22
    @7
    @5
    @22
    c1
    clt
    breq2
    rspcev
    syl2anc
    ex
    rexlimdvva
    mpd
end
