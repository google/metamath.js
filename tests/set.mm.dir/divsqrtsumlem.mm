include "crp.mm"
include "cr.mm"
include "wf.mm"
include "crli.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "c1.mm"
include "csqrt.mm"
include "cdiv.mm"
include "cle.mm"
include "wi.mm"
include "wtru.mm"
include "cc0.mm"
include "w3a.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "cn.mm"
include "cpnf.mm"
include "cioo.mm"
include "ioorp.mm"
include "eqcomi.mm"
include "nnuz.mm"
include "1zzd.mm"
include "0red.mm"
include "caddc.mm"
include "1re.mm"
include "0nn0.mm"
include "nn0addge2i.mm"
include "a1i.mm"
include "2re.mm"
include "rpsqrtcl.mm"
include "adantl.mm"
include "rpred.mm"
include "remulcl.mm"
include "sylancr.mm"
include "rprecred.mm"
include "nnrp.mm"
include "sylan2.mm"
include "cmpt.mm"
include "cdv.mm"
include "cc.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "rpcnd.mm"
include "2rp.mm"
include "rpmulcl.mm"
include "rpreccld.mm"
include "wceq.mm"
include "dvsqrt.mm"
include "2cnd.mm"
include "dvmptcmul.mm"
include "wne.mm"
include "1cnd.mm"
include "rpcnne0d.mm"
include "divass.mm"
include "syl3anc.mm"
include "rpcnne0.mm"
include "mp1i.mm"
include "divcan5.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "simp3r.mm"
include "wb.mm"
include "simp2l.mm"
include "rprege0d.mm"
include "simp2r.mm"
include "sqrtle.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "rpsqrtcld.mm"
include "lerecd.mm"
include "sqrtlim.mm"
include "dvfsumrlim3.mm"
include "simp1d.mm"
include "trud.mm"
include "simp2d.mm"
include "rpge0.mm"
include "simp3d.mm"
include "mpd3an3.mm"
include "3pm3.2i.mm"

theorem divsqrtsumlem
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cL: class L
  let vy: setvar y
  let wph: wff ph
  assume divsqrtsum.2: |- F = ( x e. RR+ |-> ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( 1 / ( sqrt ` n ) ) - ( 2 x. ( sqrt ` x ) ) ) )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint x y
  disjoint F y
  disjoint L y
  disjoint n y
  disjoint n ph
  disjoint ph y
  assert |- ( F : RR+ --> RR /\ F e. dom ~~>r /\ ( ( F ~~>r L /\ A e. RR+ ) -> ( abs ` ( ( F ` A ) - L ) ) <_ ( 1 / ( sqrt ` A ) ) ) )

  proof
    crp
    cr
    cF
    wf
    #
    cF
    crli
    cdm
    wcel
    #
    cF
    cL
    crli
    wbr
    #
    cA
    crp
    wcel
    #
    wa
    cA
    cF
    cfv
    cL
    cmin
    co
    cabs
    cfv
    c1
    cA
    csqrt
    cfv
    #
    cdiv
    co
    #
    cle
    wbr
    #
    wi
    @0
    wtru
    @0
    @1
    @2
    @3
    cc0
    cA
    cle
    wbr
    #
    w3a
    @6
    wi
    #
    wtru
    vx
    c2
    vx
    cv
    #
    csqrt
    cfv
    #
    cmul
    co
    #
    c1
    @10
    cdiv
    co
    #
    c1
    vn
    cv
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    cc0
    crp
    cc0
    vn
    @5
    cF
    cL
    c1
    cr
    cA
    cn
    cc0
    cpnf
    cioo
    co
    crp
    ioorp
    eqcomi
    nnuz
    wtru
    1zzd
    wtru
    0red
    #
    c1
    cc0
    c1
    caddc
    co
    cle
    wbr
    wtru
    c1
    cc0
    1re
    0nn0
    nn0addge2i
    a1i
    @16
    wtru
    @9
    crp
    wcel
    #
    wa
    #
    c2
    cr
    wcel
    @10
    cr
    wcel
    @11
    cr
    wcel
    2re
    @18
    @10
    @17
    @10
    crp
    wcel
    #
    wtru
    @9
    rpsqrtcl
    adantl
    #
    rpred
    c2
    @10
    remulcl
    sylancr
    @18
    @10
    @20
    rprecred
    #
    @9
    cn
    wcel
    wtru
    @17
    @12
    cr
    wcel
    @9
    nnrp
    @21
    sylan2
    wtru
    cr
    vx
    crp
    @11
    cmpt
    cdv
    co
    vx
    crp
    c2
    c1
    @11
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    vx
    crp
    @12
    cmpt
    #
    wtru
    vx
    @10
    @22
    c2
    cr
    crp
    crp
    cr
    cr
    cc
    cpr
    wcel
    wtru
    reelprrecn
    a1i
    @18
    @10
    @20
    rpcnd
    @18
    @11
    @18
    c2
    crp
    wcel
    #
    @19
    @11
    crp
    wcel
    2rp
    @20
    c2
    @10
    rpmulcl
    sylancr
    #
    rpreccld
    cr
    vx
    crp
    @10
    cmpt
    cdv
    co
    vx
    crp
    @22
    cmpt
    wceq
    wtru
    vx
    dvsqrt
    a1i
    wtru
    2cnd
    dvmptcmul
    wtru
    vx
    crp
    @23
    @12
    @18
    c2
    c1
    cmul
    co
    @11
    cdiv
    co
    #
    @23
    @12
    @18
    c2
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @11
    cc
    wcel
    @11
    cc0
    wne
    wa
    @27
    @23
    wceq
    @18
    2cnd
    @18
    1cnd
    #
    @18
    @11
    @26
    rpcnne0d
    c2
    c1
    @11
    divass
    syl3anc
    @18
    @29
    @10
    cc
    wcel
    @10
    cc0
    wne
    wa
    @28
    c2
    cc0
    wne
    wa
    #
    @27
    @12
    wceq
    @30
    @18
    @10
    @20
    rpcnne0d
    @25
    @31
    @18
    2rp
    c2
    rpcnne0
    mp1i
    c1
    @10
    c2
    divcan5
    syl3anc
    eqtr3d
    mpteq2dva
    eqtrd
    @9
    @13
    wceq
    @10
    @14
    c1
    cdiv
    @9
    @13
    csqrt
    fveq2
    oveq2d
    wtru
    @17
    @13
    crp
    wcel
    #
    wa
    #
    cc0
    @9
    cle
    wbr
    #
    @9
    @13
    cle
    wbr
    #
    wa
    #
    w3a
    #
    @10
    @14
    cle
    wbr
    #
    @15
    @12
    cle
    wbr
    @37
    @35
    @38
    wtru
    @33
    @34
    @35
    simp3r
    @37
    @9
    cr
    wcel
    @34
    wa
    @13
    cr
    wcel
    cc0
    @13
    cle
    wbr
    wa
    @35
    @38
    wb
    @37
    @9
    wtru
    @17
    @32
    @36
    simp2l
    #
    rprege0d
    @37
    @13
    wtru
    @17
    @32
    @36
    simp2r
    #
    rprege0d
    @9
    @13
    sqrtle
    syl2anc
    mpbid
    @37
    @10
    @14
    @37
    @9
    @39
    rpsqrtcld
    @37
    @13
    @40
    rpsqrtcld
    lerecd
    mpbid
    divsqrtsum.2
    @24
    cc0
    crli
    wbr
    wtru
    vx
    sqrtlim
    a1i
    @9
    cA
    wceq
    @10
    @4
    c1
    cdiv
    @9
    cA
    csqrt
    fveq2
    oveq2d
    dvfsumrlim3
    #
    simp1d
    trud
    @1
    wtru
    @0
    @1
    @8
    @41
    simp2d
    trud
    @2
    @3
    @7
    @6
    @3
    @7
    @2
    cA
    rpge0
    adantl
    @8
    wtru
    @0
    @1
    @8
    @41
    simp3d
    trud
    mpd3an3
    3pm3.2i
end
