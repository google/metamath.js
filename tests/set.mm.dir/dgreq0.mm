include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "c0p.mm"
include "wceq.mm"
include "cc0.mm"
include "cn0.mm"
include "csn.mm"
include "cxp.mm"
include "ccoe.mm"
include "fveq2.mm"
include "syl5eq.mm"
include "coe0.mm"
include "syl6eq.mm"
include "cdgr.mm"
include "dgr0.mm"
include "fveq12d.mm"
include "0nn0.mm"
include "fvconst2g.mm"
include "mp2an.mm"
include "wa.mm"
include "cc.mm"
include "coefv0.mm"
include "adantr.mm"
include "cn.mm"
include "wn.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "simpr.mm"
include "nnred.mm"
include "ltm1d.mm"
include "cle.mm"
include "caddc.mm"
include "cuz.mm"
include "cima.mm"
include "simpll.mm"
include "nnm1nn0.mm"
include "adantl.mm"
include "cv.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "dgrub.mm"
include "3expia.mm"
include "ad2ant2rl.mm"
include "simplr.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "necon3d.mm"
include "jcad.mm"
include "cr.mm"
include "nn0re.mm"
include "ad2antll.mm"
include "nnre.mm"
include "ad2antrl.mm"
include "ltlend.mm"
include "cz.mm"
include "wb.mm"
include "nn0z.mm"
include "nnz.mm"
include "zltlem1.mm"
include "syl2anc.mm"
include "bitr3d.mm"
include "sylibd.mm"
include "expr.mm"
include "ralrimiv.mm"
include "wf.mm"
include "coef3.mm"
include "ad2antrr.mm"
include "plyco0.mm"
include "mpbird.mm"
include "dgrlb.mm"
include "syl3anc.mm"
include "peano2rem.mm"
include "syl.mm"
include "lenltd.mm"
include "mpbid.mm"
include "pm2.65da.mm"
include "wo.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "mpd.mm"
include "fveq2d.mm"
include "3eqtr2d.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "syl5eqr.mm"
include "0dgrb.mm"
include "df-0p.mm"
include "a1i.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "impbid2.mm"

theorem dgreq0
  let cA: class A
  let cS: class S
  let cF: class F
  let cN: class N
  let vk: setvar k
  let vz: setvar z
  assume dgreq0.1: |- N = ( deg ` F )
  assume dgreq0.2: |- A = ( coeff ` F )


  assert |- ( F e. ( Poly ` S ) -> ( F = 0p <-> ( A ` N ) = 0 ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cF
    c0p
    wceq
    #
    cN
    cA
    cfv
    #
    cc0
    wceq
    #
    @1
    @2
    cc0
    cn0
    cc0
    csn
    #
    cxp
    #
    cfv
    #
    cc0
    @1
    cN
    cc0
    cA
    @5
    @1
    cA
    c0p
    ccoe
    cfv
    #
    @5
    @1
    cA
    cF
    ccoe
    cfv
    @7
    dgreq0.2
    cF
    c0p
    ccoe
    fveq2
    syl5eq
    coe0
    syl6eq
    @1
    cN
    c0p
    cdgr
    cfv
    #
    cc0
    @1
    cN
    cF
    cdgr
    cfv
    #
    @8
    dgreq0.1
    cF
    c0p
    cdgr
    fveq2
    syl5eq
    dgr0
    syl6eq
    fveq12d
    cc0
    cn0
    wcel
    #
    @10
    @6
    cc0
    wceq
    0nn0
    0nn0
    cn0
    cc0
    cc0
    cn0
    fvconst2g
    mp2an
    syl6eq
    @0
    @3
    @1
    @0
    @3
    wa
    #
    cc
    cc0
    cF
    cfv
    #
    csn
    #
    cxp
    #
    cc
    @4
    cxp
    #
    cF
    c0p
    @11
    @13
    @4
    cc
    @11
    @12
    cc0
    @11
    @12
    cc0
    cA
    cfv
    #
    @2
    cc0
    @0
    @12
    @16
    wceq
    @3
    cA
    cS
    cF
    dgreq0.2
    coefv0
    adantr
    @11
    cN
    cc0
    cA
    @11
    cN
    cn
    wcel
    #
    wn
    cN
    cc0
    wceq
    #
    @11
    @17
    cN
    c1
    cmin
    co
    #
    cN
    clt
    wbr
    #
    @11
    @17
    wa
    #
    cN
    @21
    cN
    @11
    @17
    simpr
    nnred
    ltm1d
    @21
    cN
    @19
    cle
    wbr
    #
    @20
    wn
    @21
    @0
    @19
    cn0
    wcel
    #
    cA
    @19
    c1
    caddc
    co
    cuz
    cfv
    cima
    @4
    wceq
    #
    @22
    @0
    @3
    @17
    simpll
    @17
    @23
    @11
    cN
    nnm1nn0
    adantl
    #
    @21
    @24
    vk
    cv
    #
    cA
    cfv
    #
    cc0
    wne
    #
    @26
    @19
    cle
    wbr
    #
    wi
    #
    vk
    cn0
    wral
    #
    @21
    @30
    vk
    cn0
    @11
    @17
    @26
    cn0
    wcel
    #
    @30
    @11
    @17
    @32
    wa
    #
    wa
    #
    @28
    @26
    cN
    cle
    wbr
    #
    cN
    @26
    wne
    #
    wa
    #
    @29
    @34
    @28
    @35
    @36
    @0
    @32
    @28
    @35
    wi
    @3
    @17
    @0
    @32
    @28
    @35
    cA
    cS
    cF
    @26
    cN
    dgreq0.2
    dgreq0.1
    dgrub
    3expia
    ad2ant2rl
    @34
    cN
    @26
    @27
    cc0
    @34
    @3
    cN
    @26
    wceq
    #
    @27
    cc0
    wceq
    @0
    @3
    @33
    simplr
    @38
    @2
    @27
    cc0
    cN
    @26
    cA
    fveq2
    eqeq1d
    syl5ibcom
    necon3d
    jcad
    @34
    @26
    cN
    clt
    wbr
    #
    @37
    @29
    @34
    @26
    cN
    @32
    @26
    cr
    wcel
    @11
    @17
    @26
    nn0re
    ad2antll
    @17
    cN
    cr
    wcel
    #
    @11
    @32
    cN
    nnre
    #
    ad2antrl
    ltlend
    @34
    @26
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @39
    @29
    wb
    @32
    @42
    @11
    @17
    @26
    nn0z
    ad2antll
    @17
    @43
    @11
    @32
    cN
    nnz
    ad2antrl
    @26
    cN
    zltlem1
    syl2anc
    bitr3d
    sylibd
    expr
    ralrimiv
    @21
    @23
    cn0
    cc
    cA
    wf
    #
    @24
    @31
    wb
    @25
    @0
    @44
    @3
    @17
    cA
    cS
    cF
    dgreq0.2
    coef3
    ad2antrr
    cA
    vk
    @19
    plyco0
    syl2anc
    mpbird
    cA
    cS
    cF
    @19
    cN
    dgreq0.2
    dgreq0.1
    dgrlb
    syl3anc
    @21
    cN
    @19
    @17
    @40
    @11
    @41
    adantl
    #
    @21
    @40
    @19
    cr
    wcel
    @45
    cN
    peano2rem
    syl
    lenltd
    mpbid
    pm2.65da
    @11
    @17
    @18
    @11
    cN
    cn0
    wcel
    #
    @17
    @18
    wo
    @0
    @46
    @3
    @0
    cN
    @9
    cn0
    dgreq0.1
    cS
    cF
    dgrcl
    syl5eqel
    adantr
    cN
    elnn0
    sylib
    ord
    mpd
    #
    fveq2d
    @0
    @3
    simpr
    3eqtr2d
    sneqd
    xpeq2d
    @11
    @9
    cc0
    wceq
    #
    cF
    @14
    wceq
    #
    @11
    @9
    cN
    cc0
    dgreq0.1
    @47
    syl5eqr
    @0
    @48
    @49
    wb
    @3
    cS
    cF
    0dgrb
    adantr
    mpbid
    c0p
    @15
    wceq
    @11
    df-0p
    a1i
    3eqtr4d
    ex
    impbid2
end
