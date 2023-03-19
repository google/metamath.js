include "cfn.mm"
include "wcel.mm"
include "cn.mm"
include "wf.mm"
include "cn0.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "wrex.mm"
include "cmap.mm"
include "vdw.mm"
include "3adant2.mm"
include "wa.mm"
include "cres.mm"
include "wi.mm"
include "wss.mm"
include "simpl2.mm"
include "cuz.mm"
include "cfv.mm"
include "fzssuz.mm"
include "nnuz.mm"
include "sseqtr4i.mm"
include "fssres.mm"
include "sylancl.mm"
include "cvv.mm"
include "wb.mm"
include "simpl1.mm"
include "ovex.mm"
include "elmapg.mm"
include "mpbird.mm"
include "wceq.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eleq2d.mm"
include "ralbidv.mm"
include "2rexbidv.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "resss.mm"
include "cnvss.mm"
include "imass1.mm"
include "mp2b.mm"
include "sseli.mm"
include "ralimi.mm"
include "reximi.mm"
include "syl6.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem vdwnnlem1
  let cR: class R
  let vm: setvar m
  let cF: class F
  let cK: class K
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let cA: class A
  let vf: setvar f
  let vn: setvar n
  let vx: setvar x
  let wph: wff ph
  let cB: class B
  let cS: class S

  disjoint a d
  disjoint a m
  disjoint d m
  disjoint a c
  disjoint K a
  disjoint c d
  disjoint c m
  disjoint K c
  disjoint K d
  disjoint K m
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint F a
  disjoint F c
  disjoint F d
  disjoint F m
  disjoint a k
  disjoint A a
  disjoint d k
  disjoint A d
  disjoint k m
  disjoint A k
  disjoint A m
  disjoint a f
  disjoint a n
  disjoint c f
  disjoint c n
  disjoint d f
  disjoint d n
  disjoint f m
  disjoint f n
  disjoint K f
  disjoint m n
  disjoint K n
  disjoint a x
  disjoint a ph
  disjoint c x
  disjoint c ph
  disjoint d x
  disjoint d ph
  disjoint ph x
  disjoint f x
  disjoint R f
  disjoint n x
  disjoint R n
  disjoint R x
  disjoint B a
  disjoint B d
  disjoint B k
  disjoint B m
  disjoint c k
  disjoint f k
  disjoint F f
  disjoint k n
  disjoint F k
  disjoint F n
  disjoint S a
  disjoint S d
  disjoint k x
  disjoint S k
  disjoint m x
  disjoint S m
  disjoint S x
  assert |- ( ( R e. Fin /\ F : NN --> R /\ K e. NN0 ) -> E. c e. R E. a e. NN E. d e. NN A. m e. ( 0 ... ( K - 1 ) ) ( a + ( m x. d ) ) e. ( `' F " { c } ) )

  proof
    cR
    cfn
    wcel
    #
    cn
    cR
    cF
    wf
    #
    cK
    cn0
    wcel
    #
    w3a
    #
    va
    cv
    vm
    cv
    vd
    cv
    cmul
    co
    caddc
    co
    #
    vf
    cv
    #
    ccnv
    #
    vc
    cv
    csn
    #
    cima
    #
    wcel
    #
    vm
    cc0
    cK
    c1
    cmin
    co
    cfz
    co
    #
    wral
    #
    vd
    cn
    wrex
    va
    cn
    wrex
    #
    vc
    cR
    wrex
    #
    vf
    cR
    c1
    vn
    cv
    #
    cfz
    co
    #
    cmap
    co
    #
    wral
    #
    vn
    cn
    wrex
    #
    @4
    cF
    ccnv
    #
    @7
    cima
    #
    wcel
    #
    vm
    @10
    wral
    #
    vd
    cn
    wrex
    #
    va
    cn
    wrex
    #
    vc
    cR
    wrex
    #
    @0
    @2
    @18
    @1
    cR
    vf
    vm
    vn
    cK
    va
    vc
    vd
    vdw
    3adant2
    @3
    @17
    @25
    vn
    cn
    @3
    @14
    cn
    wcel
    #
    wa
    #
    @17
    @4
    cF
    @15
    cres
    #
    ccnv
    #
    @7
    cima
    #
    wcel
    #
    vm
    @10
    wral
    #
    vd
    cn
    wrex
    #
    va
    cn
    wrex
    #
    vc
    cR
    wrex
    #
    @25
    @27
    @28
    @16
    wcel
    #
    @17
    @35
    wi
    @27
    @36
    @15
    cR
    @28
    wf
    #
    @27
    @1
    @15
    cn
    wss
    @37
    @0
    @1
    @2
    @26
    simpl2
    @15
    c1
    cuz
    cfv
    cn
    c1
    @14
    fzssuz
    nnuz
    sseqtr4i
    cn
    cR
    @15
    cF
    fssres
    sylancl
    @27
    @0
    @15
    cvv
    wcel
    @36
    @37
    wb
    @0
    @1
    @2
    @26
    simpl1
    c1
    @14
    cfz
    ovex
    cR
    @15
    @28
    cfn
    cvv
    elmapg
    sylancl
    mpbird
    @13
    @35
    vf
    @28
    @16
    @5
    @28
    wceq
    #
    @12
    @34
    vc
    cR
    @38
    @11
    @32
    va
    vd
    cn
    cn
    @38
    @9
    @31
    vm
    @10
    @38
    @8
    @30
    @4
    @38
    @6
    @29
    @7
    @5
    @28
    cnveq
    imaeq1d
    eleq2d
    ralbidv
    2rexbidv
    rexbidv
    rspcv
    syl
    @34
    @24
    vc
    cR
    @33
    @23
    va
    cn
    @32
    @22
    vd
    cn
    @31
    @21
    vm
    @10
    @30
    @20
    @4
    @28
    cF
    wss
    @29
    @19
    wss
    @30
    @20
    wss
    cF
    @15
    resss
    @28
    cF
    cnvss
    @29
    @19
    @7
    imass1
    mp2b
    sseli
    ralimi
    reximi
    reximi
    reximi
    syl6
    rexlimdva
    mpd
end
