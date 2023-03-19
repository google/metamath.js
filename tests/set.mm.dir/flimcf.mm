include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "cflim.mm"
include "co.mm"
include "cfil.mm"
include "wral.mm"
include "simplll.mm"
include "simprl.mm"
include "simplr.mm"
include "flimss1.mm"
include "syl3anc.mm"
include "simprr.mm"
include "sseldd.mm"
include "expr.mm"
include "ssrdv.mm"
include "ralrimiva.mm"
include "csn.mm"
include "cnei.mm"
include "c0.mm"
include "wne.mm"
include "simpllr.mm"
include "toponss.mm"
include "syl2anc.mm"
include "snssd.mm"
include "snnzg.mm"
include "syl.mm"
include "neifil.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "neiflim.mm"
include "flimneiss.mm"
include "ctop.mm"
include "topontop.mm"
include "opnneip.mm"
include "anassrs.mm"
include "wb.mm"
include "opnnei.mm"
include "3syl.mm"
include "mpbird.mm"
include "ex.mm"
include "impbida.mm"

theorem flimcf
  let vf: setvar f
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cY: class Y

  disjoint J f
  disjoint K f
  disjoint X f
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint K x
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` X ) ) -> ( J C_ K <-> A. f e. ( Fil ` X ) ( K fLim f ) C_ ( J fLim f ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cK
    @0
    wcel
    #
    wa
    #
    cJ
    cK
    wss
    #
    cK
    vf
    cv
    #
    cflim
    co
    #
    cJ
    @5
    cflim
    co
    #
    wss
    #
    vf
    cX
    cfil
    cfv
    #
    wral
    #
    @3
    @4
    wa
    #
    @8
    vf
    @9
    @11
    @5
    @9
    wcel
    #
    wa
    vx
    @6
    @7
    @11
    @12
    vx
    cv
    #
    @6
    wcel
    #
    @13
    @7
    wcel
    @11
    @12
    @14
    wa
    #
    wa
    #
    @6
    @7
    @13
    @16
    @1
    @12
    @4
    @8
    @1
    @2
    @4
    @15
    simplll
    @11
    @12
    @14
    simprl
    @3
    @4
    @15
    simplr
    @5
    cJ
    cK
    cX
    flimss1
    syl3anc
    @11
    @12
    @14
    simprr
    sseldd
    expr
    ssrdv
    ralrimiva
    @3
    @10
    wa
    #
    vx
    cJ
    cK
    @17
    @13
    cJ
    wcel
    #
    @13
    cK
    wcel
    #
    @17
    @18
    wa
    #
    @19
    @13
    vy
    cv
    #
    csn
    #
    cK
    cnei
    cfv
    cfv
    #
    wcel
    #
    vy
    @13
    wral
    #
    @20
    @24
    vy
    @13
    @17
    @18
    @21
    @13
    wcel
    #
    @24
    @17
    @18
    @26
    wa
    #
    wa
    #
    @22
    cJ
    cnei
    cfv
    cfv
    #
    @23
    @13
    @28
    @21
    cJ
    @23
    cflim
    co
    #
    wcel
    @29
    @23
    wss
    @28
    cK
    @23
    cflim
    co
    #
    @30
    @21
    @28
    @23
    @9
    wcel
    #
    @10
    @31
    @30
    wss
    #
    @28
    @2
    @22
    cX
    wss
    @22
    c0
    wne
    #
    @32
    @1
    @2
    @10
    @27
    simpllr
    #
    @28
    @21
    cX
    @28
    @13
    cX
    @21
    @28
    @1
    @18
    @13
    cX
    wss
    @1
    @2
    @10
    @27
    simplll
    #
    @17
    @18
    @26
    simprl
    #
    @13
    cJ
    cX
    toponss
    syl2anc
    @17
    @18
    @26
    simprr
    #
    sseldd
    #
    snssd
    @28
    @21
    cX
    wcel
    #
    @34
    @39
    @21
    cX
    snnzg
    syl
    @22
    cK
    cX
    neifil
    syl3anc
    @3
    @10
    @27
    simplr
    @8
    @33
    vf
    @23
    @9
    @5
    @23
    wceq
    @6
    @31
    @7
    @30
    @5
    @23
    cK
    cflim
    oveq2
    @5
    @23
    cJ
    cflim
    oveq2
    sseq12d
    rspcv
    sylc
    @28
    @2
    @40
    @21
    @31
    wcel
    @35
    @39
    @21
    cK
    cX
    neiflim
    syl2anc
    sseldd
    @21
    @23
    cJ
    flimneiss
    syl
    @28
    cJ
    ctop
    wcel
    #
    @18
    @26
    @13
    @29
    wcel
    @28
    @1
    @41
    @36
    cX
    cJ
    topontop
    syl
    @37
    @38
    @21
    cJ
    @13
    opnneip
    syl3anc
    sseldd
    anassrs
    ralrimiva
    @20
    @2
    cK
    ctop
    wcel
    @19
    @25
    wb
    @1
    @2
    @10
    @18
    simpllr
    cX
    cK
    topontop
    vy
    @13
    cK
    opnnei
    3syl
    mpbird
    ex
    ssrdv
    impbida
end
