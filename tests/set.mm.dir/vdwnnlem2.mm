include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
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
include "wn.mm"
include "wss.mm"
include "wi.mm"
include "cz.mm"
include "eluzel2.mm"
include "peano2zm.mm"
include "syl.mm"
include "id.mm"
include "cc.mm"
include "wceq.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "eluzp1m1.mm"
include "syl2anc.mm"
include "ad2antlr.mm"
include "fzss2.mm"
include "ssralv.mm"
include "3syl.mm"
include "reximdv.mm"
include "con3d.mm"
include "simpr.mm"
include "eluznn.mm"
include "syl2anr.mm"
include "jctild.mm"
include "expimpd.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "2rexbidv.mm"
include "notbid.mm"
include "elrab2.mm"
include "3imtr4g.mm"

theorem vdwnnlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vn: setvar n
  let cK: class K
  let vx: setvar x
  assume vdwnn.1: |- ( ph -> R e. Fin )
  assume vdwnn.2: |- ( ph -> F : NN --> R )
  assume vdwnn.3: |- S = { k e. NN | -. E. a e. NN E. d e. NN A. m e. ( 0 ... ( k - 1 ) ) ( a + ( m x. d ) ) e. ( `' F " { c } ) }

  disjoint a d
  disjoint a k
  disjoint a m
  disjoint A a
  disjoint d k
  disjoint d m
  disjoint A d
  disjoint k m
  disjoint A k
  disjoint A m
  disjoint a c
  disjoint c d
  disjoint c m
  disjoint a ph
  disjoint c ph
  disjoint d ph
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint B a
  disjoint B d
  disjoint B k
  disjoint B m
  disjoint F a
  disjoint c k
  disjoint F c
  disjoint F d
  disjoint F k
  disjoint F m
  disjoint S a
  disjoint S d
  disjoint S k
  disjoint S m
  disjoint a f
  disjoint a n
  disjoint K a
  disjoint c f
  disjoint c n
  disjoint K c
  disjoint d f
  disjoint d n
  disjoint K d
  disjoint f m
  disjoint f n
  disjoint K f
  disjoint m n
  disjoint K m
  disjoint K n
  disjoint a x
  disjoint c x
  disjoint d x
  disjoint ph x
  disjoint f x
  disjoint R f
  disjoint n x
  disjoint R n
  disjoint R x
  disjoint f k
  disjoint F f
  disjoint k n
  disjoint F n
  disjoint k x
  disjoint m x
  disjoint S x
  assert |- ( ( ph /\ B e. ( ZZ>= ` A ) ) -> ( A e. S -> B e. S ) )

  proof
    wph
    cB
    cA
    cuz
    cfv
    #
    wcel
    #
    wa
    #
    cA
    cn
    wcel
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
    cF
    ccnv
    vc
    cv
    csn
    cima
    wcel
    #
    vm
    cc0
    cA
    c1
    cmin
    co
    #
    cfz
    co
    #
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
    wn
    #
    wa
    cB
    cn
    wcel
    #
    @4
    vm
    cc0
    cB
    c1
    cmin
    co
    #
    cfz
    co
    #
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
    wn
    #
    wa
    #
    cA
    cS
    wcel
    cB
    cS
    wcel
    @2
    @3
    @10
    @18
    @2
    @3
    wa
    #
    @10
    @17
    @11
    @19
    @16
    @9
    @19
    @15
    @8
    va
    cn
    @19
    @14
    @7
    vd
    cn
    @19
    @12
    @5
    cuz
    cfv
    wcel
    #
    @6
    @13
    wss
    @14
    @7
    wi
    @1
    @20
    wph
    @3
    @1
    @5
    cz
    wcel
    #
    cB
    @5
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @20
    @1
    cA
    cz
    wcel
    @21
    cA
    cB
    eluzel2
    #
    cA
    peano2zm
    syl
    @1
    cB
    @0
    @23
    @1
    id
    @1
    @22
    cA
    cuz
    @1
    cA
    cc
    wcel
    c1
    cc
    wcel
    @22
    cA
    wceq
    @1
    cA
    @24
    zcnd
    ax-1cn
    cA
    c1
    npcan
    sylancl
    fveq2d
    eleqtrrd
    @5
    cB
    eluzp1m1
    syl2anc
    ad2antlr
    @5
    cc0
    @12
    fzss2
    @4
    vm
    @6
    @13
    ssralv
    3syl
    reximdv
    reximdv
    con3d
    @3
    @3
    @1
    @11
    @2
    @3
    id
    wph
    @1
    simpr
    cB
    cA
    eluznn
    syl2anr
    jctild
    expimpd
    @4
    vm
    cc0
    vk
    cv
    #
    c1
    cmin
    co
    #
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
    wn
    #
    @10
    vk
    cA
    cn
    cS
    @25
    cA
    wceq
    #
    @29
    @9
    @31
    @28
    @7
    va
    vd
    cn
    cn
    @31
    @4
    vm
    @27
    @6
    @31
    @26
    @5
    cc0
    cfz
    @25
    cA
    c1
    cmin
    oveq1
    oveq2d
    raleqdv
    2rexbidv
    notbid
    vdwnn.3
    elrab2
    @30
    @17
    vk
    cB
    cn
    cS
    @25
    cB
    wceq
    #
    @29
    @16
    @32
    @28
    @14
    va
    vd
    cn
    cn
    @32
    @4
    vm
    @27
    @13
    @32
    @26
    @12
    cc0
    cfz
    @25
    cB
    c1
    cmin
    oveq1
    oveq2d
    raleqdv
    2rexbidv
    notbid
    vdwnn.3
    elrab2
    3imtr4g
end
