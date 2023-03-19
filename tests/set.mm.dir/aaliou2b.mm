include "caa.mm"
include "wcel.mm"
include "cr.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cexp.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cn.mm"
include "wral.mm"
include "cz.mm"
include "crp.mm"
include "wrex.mm"
include "wa.mm"
include "cin.mm"
include "elin.mm"
include "aaliou2.mm"
include "sylbir.mm"
include "wn.mm"
include "c1.mm"
include "cim.mm"
include "c2.mm"
include "1nn.mm"
include "a1i.mm"
include "cc.mm"
include "aacn.mm"
include "adantr.mm"
include "imcld.mm"
include "recnd.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "reim0b.mm"
include "syl.mm"
include "necon3bbid.mm"
include "biimpa.mm"
include "absrpcld.mm"
include "rphalfcld.mm"
include "cn0.mm"
include "1nn0.mm"
include "nnexpcl.mm"
include "mpan2.mm"
include "ad2antll.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "cq.mm"
include "znq.mm"
include "adantl.mm"
include "qre.mm"
include "subcld.mm"
include "abscld.mm"
include "cle.mm"
include "nnge1d.mm"
include "1rp.mm"
include "rpregt0.mm"
include "mp1i.mm"
include "rpregt0d.mm"
include "lediv2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "rpcnd.mm"
include "div1d.mm"
include "breqtrd.mm"
include "rphalflt.mm"
include "imsubd.mm"
include "reim0d.mm"
include "oveq2d.mm"
include "subid1d.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "absimle.mm"
include "eqbrtrrd.mm"
include "ltletrd.mm"
include "lelttrd.mm"
include "olcd.mm"
include "ralrimivva.mm"
include "oveq2.mm"
include "breq1d.mm"
include "orbi2d.mm"
include "2ralbidv.mm"
include "oveq1.mm"
include "rspc2ev.mm"
include "pm2.61dan.mm"

theorem aaliou2b
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  let vq: setvar q
  let vp: setvar p
  let va: setvar a

  disjoint A k
  disjoint A x
  disjoint A p
  disjoint A q
  disjoint k x
  disjoint k p
  disjoint k q
  disjoint p x
  disjoint q x
  disjoint p q
  disjoint A a
  disjoint a k
  disjoint a x
  disjoint a p
  disjoint a q
  assert |- ( A e. AA -> E. k e. NN E. x e. RR+ A. p e. ZZ A. q e. NN ( A = ( p / q ) \/ ( x / ( q ^ k ) ) < ( abs ` ( A - ( p / q ) ) ) ) )

  proof
    cA
    caa
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    vp
    cv
    #
    vq
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vx
    cv
    #
    @3
    vk
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cA
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    wo
    #
    vq
    cn
    wral
    vp
    cz
    wral
    #
    vx
    crp
    wrex
    vk
    cn
    wrex
    #
    @0
    @1
    wa
    cA
    caa
    cr
    cin
    wcel
    @15
    cA
    caa
    cr
    elin
    vx
    cA
    vk
    vq
    vp
    aaliou2
    sylbir
    @0
    @1
    wn
    #
    wa
    #
    c1
    cn
    wcel
    #
    cA
    cim
    cfv
    #
    cabs
    cfv
    #
    c2
    cdiv
    co
    #
    crp
    wcel
    #
    @5
    @21
    @3
    c1
    cexp
    co
    #
    cdiv
    co
    #
    @11
    clt
    wbr
    #
    wo
    #
    vq
    cn
    wral
    vp
    cz
    wral
    #
    @15
    @18
    @17
    1nn
    a1i
    @17
    @20
    @17
    @19
    @17
    @19
    @17
    cA
    @0
    cA
    cc
    wcel
    #
    @16
    cA
    aacn
    #
    adantr
    #
    imcld
    recnd
    #
    @0
    @16
    @19
    cc0
    wne
    @0
    @1
    @19
    cc0
    @0
    @28
    @1
    @19
    cc0
    wceq
    wb
    @29
    cA
    reim0b
    syl
    necon3bbid
    biimpa
    absrpcld
    #
    rphalfcld
    #
    @17
    @26
    vp
    vq
    cz
    cn
    @17
    @2
    cz
    wcel
    #
    @3
    cn
    wcel
    #
    wa
    #
    wa
    #
    @25
    @5
    @37
    @24
    @21
    @11
    @37
    @24
    @37
    @21
    @23
    @17
    @22
    @36
    @33
    adantr
    #
    @37
    @23
    @35
    @23
    cn
    wcel
    #
    @17
    @34
    @35
    c1
    cn0
    wcel
    @39
    1nn0
    @3
    c1
    nnexpcl
    mpan2
    ad2antll
    #
    nnrpd
    #
    rpdivcld
    rpred
    @37
    @21
    @38
    rpred
    #
    @37
    @10
    @37
    cA
    @4
    @17
    @28
    @36
    @30
    adantr
    #
    @37
    @4
    @37
    @4
    cq
    wcel
    #
    @4
    cr
    wcel
    @36
    @44
    @17
    @2
    @3
    znq
    adantl
    @4
    qre
    syl
    #
    recnd
    #
    subcld
    #
    abscld
    #
    @37
    @24
    @21
    c1
    cdiv
    co
    #
    @21
    cle
    @37
    c1
    @23
    cle
    wbr
    #
    @24
    @49
    cle
    wbr
    #
    @37
    @23
    @40
    nnge1d
    @37
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    wa
    #
    @23
    cr
    wcel
    cc0
    @23
    clt
    wbr
    wa
    @21
    cr
    wcel
    cc0
    @21
    clt
    wbr
    wa
    @50
    @51
    wb
    c1
    crp
    wcel
    @52
    @37
    1rp
    c1
    rpregt0
    mp1i
    @37
    @23
    @41
    rpregt0d
    @37
    @21
    @38
    rpregt0d
    c1
    @23
    @21
    lediv2
    syl3anc
    mpbid
    @37
    @21
    @37
    @21
    @38
    rpcnd
    div1d
    breqtrd
    @37
    @21
    @20
    @11
    @42
    @37
    @20
    @17
    @20
    crp
    wcel
    #
    @36
    @32
    adantr
    #
    rpred
    @48
    @37
    @53
    @21
    @20
    clt
    wbr
    @54
    @20
    rphalflt
    syl
    @37
    @10
    cim
    cfv
    #
    cabs
    cfv
    #
    @20
    @11
    cle
    @37
    @55
    @19
    cabs
    @37
    @55
    @19
    @4
    cim
    cfv
    #
    cmin
    co
    @19
    cc0
    cmin
    co
    @19
    @37
    cA
    @4
    @43
    @46
    imsubd
    @37
    @57
    cc0
    @19
    cmin
    @37
    @4
    @45
    reim0d
    oveq2d
    @37
    @19
    @17
    @19
    cc
    wcel
    @36
    @31
    adantr
    subid1d
    3eqtrd
    fveq2d
    @37
    @10
    cc
    wcel
    @56
    @11
    cle
    wbr
    @47
    @10
    absimle
    syl
    eqbrtrrd
    ltletrd
    lelttrd
    olcd
    ralrimivva
    @14
    @27
    @5
    @6
    @23
    cdiv
    co
    #
    @11
    clt
    wbr
    #
    wo
    #
    vq
    cn
    wral
    vp
    cz
    wral
    vk
    vx
    c1
    @21
    cn
    crp
    @7
    c1
    wceq
    #
    @13
    @60
    vp
    vq
    cz
    cn
    @61
    @12
    @59
    @5
    @61
    @9
    @58
    @11
    clt
    @61
    @8
    @23
    @6
    cdiv
    @7
    c1
    @3
    cexp
    oveq2
    oveq2d
    breq1d
    orbi2d
    2ralbidv
    @6
    @21
    wceq
    #
    @60
    @26
    vp
    vq
    cz
    cn
    @62
    @59
    @25
    @5
    @62
    @58
    @24
    @11
    clt
    @6
    @21
    @23
    cdiv
    oveq1
    breq1d
    orbi2d
    2ralbidv
    rspc2ev
    syl3anc
    pm2.61dan
end
