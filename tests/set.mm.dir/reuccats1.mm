include "cv.mm"
include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "cs1.mm"
include "cconcat.mm"
include "wreu.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "wi.mm"
include "eleq1w.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "cbvralv.mm"
include "wrex.mm"
include "nfel2.mm"
include "weq.mm"
include "s1eq.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "reu8nf.mm"
include "nfv.mm"
include "nfral.mm"
include "nfan.mm"
include "nfreu.mm"
include "wb.mm"
include "simprl.mm"
include "simp-4l.mm"
include "simpr.mm"
include "adantr.mm"
include "simplrr.mm"
include "simp-4r.mm"
include "reuccats1lem.mm"
include "syl32anc.mm"
include "oveq1.mm"
include "simpl.mm"
include "s1cl.mm"
include "anim12i.mm"
include "swrdccat1.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "eqcomd.mm"
include "ex.mm"
include "impbid.mm"
include "ralrimiva.mm"
include "reu6i.mm"
include "syl2anc.mm"
include "exp31.mm"
include "rexlimd.mm"
include "syl5bi.mm"
include "sylan2b.mm"

theorem reuccats1
  let vx: setvar x
  let vv: setvar v
  let cV: class V
  let cW: class W
  let cX: class X
  let vu: setvar u
  let vy: setvar y
  assume reuccats1.1: |- F/_ v X

  disjoint V v
  disjoint V x
  disjoint v x
  disjoint W v
  disjoint W x
  disjoint X x
  disjoint V u
  disjoint V y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v y
  disjoint x y
  disjoint W u
  disjoint W y
  disjoint X u
  disjoint X y
  assert |- ( ( W e. Word V /\ A. x e. X ( x e. Word V /\ ( # ` x ) = ( ( # ` W ) + 1 ) ) ) -> ( E! v e. V ( W ++ <" v "> ) e. X -> E! x e. X W = ( x substr <. 0 , ( # ` W ) >. ) ) )

  proof
    vx
    cv
    #
    cV
    cword
    #
    wcel
    #
    @0
    chash
    cfv
    #
    cW
    chash
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    vx
    cX
    wral
    cW
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    @9
    chash
    cfv
    #
    @5
    wceq
    #
    wa
    #
    vy
    cX
    wral
    #
    cW
    vv
    cv
    #
    cs1
    #
    cconcat
    co
    #
    cX
    wcel
    #
    vv
    cV
    wreu
    #
    cW
    @0
    cc0
    @4
    cop
    #
    csubstr
    co
    #
    wceq
    #
    vx
    cX
    wreu
    #
    wi
    @7
    @13
    vx
    vy
    cX
    @0
    @9
    wceq
    #
    @2
    @10
    @6
    @12
    vx
    vy
    @1
    eleq1w
    @24
    @3
    @11
    @5
    @0
    @9
    chash
    fveq2
    eqeq1d
    anbi12d
    cbvralv
    @19
    @18
    cW
    vu
    cv
    #
    cs1
    #
    cconcat
    co
    #
    cX
    wcel
    #
    @15
    @25
    wceq
    wi
    vu
    cV
    wral
    #
    wa
    #
    vv
    cV
    wrex
    @8
    @14
    wa
    #
    @23
    @18
    @28
    cW
    @0
    cs1
    #
    cconcat
    co
    #
    cX
    wcel
    vv
    vu
    vx
    cV
    vv
    @27
    cX
    reuccats1.1
    nfel2
    vv
    @33
    cX
    reuccats1.1
    nfel2
    vv
    vx
    weq
    #
    @17
    @33
    cX
    @34
    @16
    @32
    cW
    cconcat
    @15
    @0
    s1eq
    oveq2d
    eleq1d
    vx
    vu
    weq
    #
    @33
    @27
    cX
    @35
    @32
    @26
    cW
    cconcat
    @0
    @25
    s1eq
    oveq2d
    eleq1d
    reu8nf
    @31
    @30
    @23
    vv
    cV
    @8
    @14
    vv
    @8
    vv
    nfv
    @13
    vv
    vy
    cX
    reuccats1.1
    @13
    vv
    nfv
    nfral
    nfan
    @22
    vv
    vx
    cX
    reuccats1.1
    @22
    vv
    nfv
    nfreu
    @31
    @15
    cV
    wcel
    #
    @30
    @23
    @31
    @36
    wa
    #
    @30
    wa
    #
    @18
    @22
    @0
    @17
    wceq
    #
    wb
    #
    vx
    cX
    wral
    @23
    @37
    @18
    @29
    simprl
    #
    @38
    @40
    vx
    cX
    @38
    @0
    cX
    wcel
    #
    wa
    #
    @22
    @39
    @43
    @8
    @42
    @18
    @29
    @14
    @22
    @39
    wi
    @8
    @14
    @36
    @30
    @42
    simp-4l
    @38
    @42
    simpr
    @38
    @18
    @42
    @41
    adantr
    @37
    @18
    @29
    @42
    simplrr
    @8
    @14
    @36
    @30
    @42
    simp-4r
    vy
    @15
    @0
    cV
    cW
    cX
    vu
    reuccats1lem
    syl32anc
    @43
    @39
    @22
    @43
    @39
    wa
    @21
    cW
    @39
    @43
    @21
    @17
    @20
    csubstr
    co
    #
    cW
    @0
    @17
    @20
    csubstr
    oveq1
    @43
    @8
    @16
    @1
    wcel
    #
    wa
    #
    @44
    cW
    wceq
    @38
    @46
    @42
    @37
    @46
    @30
    @31
    @8
    @36
    @45
    @8
    @14
    simpl
    @15
    cV
    s1cl
    anim12i
    adantr
    adantr
    cV
    cW
    @16
    swrdccat1
    syl
    sylan9eqr
    eqcomd
    ex
    impbid
    ralrimiva
    @22
    vx
    cX
    @17
    reu6i
    syl2anc
    exp31
    rexlimd
    syl5bi
    sylan2b
end
