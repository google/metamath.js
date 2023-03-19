include "caa.mm"
include "cr.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
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
include "elin.mm"
include "cc.mm"
include "cc0.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wi.mm"
include "elaa.mm"
include "w3a.mm"
include "cdgr.mm"
include "wn.mm"
include "cxp.mm"
include "eldifn.mm"
include "3ad2ant1.mm"
include "simpr.mm"
include "fveq1.mm"
include "adantl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "recnd.mm"
include "fvex.mm"
include "fvconst2.mm"
include "syl.mm"
include "3eqtr3rd.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "eqtrd.mm"
include "df-0p.mm"
include "syl6eqr.mm"
include "velsn.mm"
include "sylibr.mm"
include "mtand.mm"
include "wb.mm"
include "eldifi.mm"
include "0dgrb.mm"
include "mtbird.mm"
include "cn0.mm"
include "dgrcl.mm"
include "elnn0.mm"
include "sylib.mm"
include "orel2.mm"
include "sylc.mm"
include "eqid.mm"
include "simp3.mm"
include "simp2.mm"
include "aaliou.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "breq1d.mm"
include "orbi2d.mm"
include "2ralbidv.mm"
include "rexbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "3exp.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "imp.mm"

theorem aaliou2
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
  assert |- ( A e. ( AA i^i RR ) -> E. k e. NN E. x e. RR+ A. p e. ZZ A. q e. NN ( A = ( p / q ) \/ ( x / ( q ^ k ) ) < ( abs ` ( A - ( p / q ) ) ) ) )

  proof
    cA
    caa
    cr
    cin
    wcel
    cA
    caa
    wcel
    #
    cA
    cr
    wcel
    #
    wa
    cA
    vp
    cv
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
    @2
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
    @3
    cmin
    co
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
    #
    vk
    cn
    wrex
    #
    cA
    caa
    cr
    elin
    @0
    @1
    @14
    @0
    cA
    cc
    wcel
    #
    cA
    va
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    va
    cz
    cply
    cfv
    #
    c0p
    csn
    #
    cdif
    #
    wrex
    #
    wa
    @1
    @14
    wi
    #
    cA
    va
    elaa
    @22
    @23
    @15
    @18
    @23
    va
    @21
    @16
    @21
    wcel
    #
    @18
    @1
    @14
    @24
    @18
    @1
    w3a
    #
    @16
    cdgr
    cfv
    #
    cn
    wcel
    #
    @4
    @5
    @2
    @26
    cexp
    co
    #
    cdiv
    co
    #
    @9
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
    #
    @14
    @25
    @26
    cc0
    wceq
    #
    wn
    @27
    @34
    wo
    #
    @27
    @25
    @34
    @16
    cc
    cc0
    @16
    cfv
    #
    csn
    #
    cxp
    #
    wceq
    #
    @25
    @39
    @16
    @20
    wcel
    #
    @24
    @18
    @40
    wn
    @1
    @16
    @19
    @20
    eldifn
    3ad2ant1
    @25
    @39
    wa
    #
    @16
    c0p
    wceq
    @40
    @41
    @16
    cc
    cc0
    csn
    #
    cxp
    #
    c0p
    @41
    @16
    @38
    @43
    @25
    @39
    simpr
    @41
    @37
    @42
    cc
    @41
    @36
    cc0
    @41
    @17
    cA
    @38
    cfv
    #
    cc0
    @36
    @39
    @17
    @44
    wceq
    @25
    cA
    @16
    @38
    fveq1
    adantl
    @24
    @18
    @1
    @39
    simpl2
    @41
    @15
    @44
    @36
    wceq
    @41
    cA
    @24
    @18
    @1
    @39
    simpl3
    recnd
    cc
    @36
    cA
    cc0
    @16
    fvex
    fvconst2
    syl
    3eqtr3rd
    sneqd
    xpeq2d
    eqtrd
    df-0p
    syl6eqr
    va
    c0p
    velsn
    sylibr
    mtand
    @25
    @16
    @19
    wcel
    #
    @34
    @39
    wb
    @24
    @18
    @45
    @1
    @16
    @19
    @20
    eldifi
    3ad2ant1
    #
    cz
    @16
    0dgrb
    syl
    mtbird
    @25
    @26
    cn0
    wcel
    #
    @35
    @25
    @45
    @47
    @46
    cz
    @16
    dgrcl
    syl
    @26
    elnn0
    sylib
    @34
    @27
    orel2
    sylc
    #
    @25
    vx
    cA
    @16
    @26
    vq
    vp
    @26
    eqid
    @46
    @48
    @24
    @18
    @1
    simp3
    @24
    @18
    @1
    simp2
    aaliou
    @13
    @33
    vk
    @26
    cn
    @6
    @26
    wceq
    #
    @12
    @32
    vx
    crp
    @49
    @11
    @31
    vp
    vq
    cz
    cn
    @49
    @10
    @30
    @4
    @49
    @8
    @29
    @9
    clt
    @49
    @7
    @28
    @5
    cdiv
    @6
    @26
    @2
    cexp
    oveq2
    oveq2d
    breq1d
    orbi2d
    2ralbidv
    rexbidv
    rspcev
    syl2anc
    3exp
    rexlimiv
    adantl
    sylbi
    imp
    sylbi
end
