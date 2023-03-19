include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
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
include "wn.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "r19.21bi.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "sseldi.mm"
include "nnred.mm"
include "ralrimiva.mm"
include "fimaxre3.mm"
include "syl2anc.mm"
include "cfl.mm"
include "cn0.mm"
include "wi.mm"
include "wf.mm"
include "1nn.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "ne0i.mm"
include "syl.mm"
include "adantr.mm"
include "r19.2z.mm"
include "ex.mm"
include "simplr.mm"
include "fllep1.mm"
include "adantlr.mm"
include "flcld.mm"
include "peano2zd.mm"
include "zred.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "cz.mm"
include "wb.mm"
include "nnzd.mm"
include "eluz.mm"
include "simpll.mm"
include "vdwnnlem2.mm"
include "impancom.mm"
include "sylbird.mm"
include "syld.mm"
include "sseli.mm"
include "nnnn0d.mm"
include "syl6.mm"
include "rexlimdva.mm"
include "simpr.mm"
include "vdwnnlem1.mm"
include "3syld.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "2rexbidv.mm"
include "notbid.mm"
include "elrab2.mm"
include "simprbi.mm"
include "ralimdva.mm"
include "ralnex.mm"
include "syl6ib.mm"
include "pm2.65d.mm"
include "nrexdv.mm"
include "pm2.65i.mm"

theorem vdwnnlem3
  let wph: wff ph
  let cR: class R
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  let vf: setvar f
  let vn: setvar n
  let cK: class K
  let vx: setvar x
  let cB: class B
  assume vdwnn.1: |- ( ph -> R e. Fin )
  assume vdwnn.2: |- ( ph -> F : NN --> R )
  assume vdwnn.3: |- S = { k e. NN | -. E. a e. NN E. d e. NN A. m e. ( 0 ... ( k - 1 ) ) ( a + ( m x. d ) ) e. ( `' F " { c } ) }
  assume vdwnn.4: |- ( ph -> A. c e. R S =/= (/) )

  disjoint a d
  disjoint a k
  disjoint a m
  disjoint d k
  disjoint d m
  disjoint k m
  disjoint a c
  disjoint c d
  disjoint c m
  disjoint a ph
  disjoint c ph
  disjoint d ph
  disjoint R a
  disjoint R c
  disjoint R d
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
  disjoint A a
  disjoint A d
  disjoint A k
  disjoint A m
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
  disjoint B a
  disjoint B d
  disjoint B k
  disjoint B m
  disjoint f k
  disjoint F f
  disjoint k n
  disjoint F n
  disjoint k x
  disjoint m x
  disjoint S x
  assert |- -. ph

  proof
    wph
    cS
    cr
    clt
    cinf
    #
    vx
    cv
    #
    cle
    wbr
    #
    vc
    cR
    wral
    #
    vx
    cr
    wrex
    #
    wph
    cR
    cfn
    wcel
    #
    @0
    cr
    wcel
    #
    vc
    cR
    wral
    @4
    vdwnn.1
    wph
    @6
    vc
    cR
    wph
    vc
    cv
    #
    cR
    wcel
    #
    wa
    #
    @0
    @9
    cS
    cn
    @0
    cS
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
    @7
    csn
    cima
    wcel
    #
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
    vk
    cn
    crab
    cn
    vdwnn.3
    @16
    vk
    cn
    ssrab2
    eqsstri
    #
    @9
    cS
    c1
    cuz
    cfv
    #
    wss
    cS
    c0
    wne
    #
    @0
    cS
    wcel
    #
    cS
    cn
    @18
    @17
    nnuz
    sseqtri
    wph
    @19
    vc
    cR
    vdwnn.4
    r19.21bi
    cS
    c1
    infssuzcl
    sylancr
    #
    sseldi
    #
    nnred
    #
    ralrimiva
    vx
    vc
    cR
    @0
    fimaxre3
    syl2anc
    wph
    @3
    vx
    cr
    wph
    @1
    cr
    wcel
    #
    wa
    #
    @3
    @10
    vm
    cc0
    @1
    cfl
    cfv
    #
    c1
    caddc
    co
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
    vc
    cR
    wrex
    #
    @25
    @3
    @2
    vc
    cR
    wrex
    #
    @27
    cn0
    wcel
    #
    @32
    @25
    cR
    c0
    wne
    #
    @3
    @33
    wi
    wph
    @35
    @24
    wph
    c1
    cF
    cfv
    #
    cR
    wcel
    #
    @35
    wph
    cn
    cR
    cF
    wf
    #
    c1
    cn
    wcel
    @37
    vdwnn.2
    1nn
    cn
    cR
    c1
    cF
    ffvelrn
    sylancl
    cR
    @36
    ne0i
    syl
    adantr
    @35
    @3
    @33
    @2
    vc
    cR
    r19.2z
    ex
    syl
    @25
    @2
    @34
    vc
    cR
    @25
    @8
    wa
    #
    @2
    @27
    cS
    wcel
    #
    @34
    @39
    @2
    @0
    @27
    cle
    wbr
    #
    @40
    @39
    @2
    @1
    @27
    cle
    wbr
    #
    @41
    @39
    @24
    @42
    wph
    @24
    @8
    simplr
    #
    @1
    fllep1
    syl
    @39
    @6
    @24
    @27
    cr
    wcel
    @2
    @42
    wa
    @41
    wi
    wph
    @8
    @6
    @24
    @23
    adantlr
    @43
    @39
    @27
    @39
    @26
    @39
    @1
    @43
    flcld
    peano2zd
    #
    zred
    @0
    @1
    @27
    letr
    syl3anc
    mpan2d
    @39
    @41
    @27
    @0
    cuz
    cfv
    wcel
    #
    @40
    @39
    @0
    cz
    wcel
    @27
    cz
    wcel
    @45
    @41
    wb
    @39
    @0
    wph
    @8
    @0
    cn
    wcel
    @24
    @22
    adantlr
    nnzd
    @44
    @0
    @27
    eluz
    syl2anc
    @39
    wph
    @20
    @45
    @40
    wi
    wph
    @24
    @8
    simpll
    wph
    @8
    @20
    @24
    @21
    adantlr
    wph
    @45
    @20
    @40
    wph
    @0
    @27
    cR
    cS
    vk
    vm
    cF
    va
    vc
    vd
    vdwnn.1
    vdwnn.2
    vdwnn.3
    vdwnnlem2
    impancom
    syl2anc
    sylbird
    syld
    #
    @40
    @27
    cS
    cn
    @27
    @17
    sseli
    nnnn0d
    syl6
    rexlimdva
    wph
    @34
    @32
    wi
    @24
    wph
    @34
    @32
    wph
    @34
    wa
    @5
    @38
    @34
    @32
    wph
    @5
    @34
    vdwnn.1
    adantr
    wph
    @38
    @34
    vdwnn.2
    adantr
    wph
    @34
    simpr
    cR
    vm
    cF
    @27
    va
    vc
    vd
    vdwnnlem1
    syl3anc
    ex
    adantr
    3syld
    @25
    @3
    @31
    wn
    #
    vc
    cR
    wral
    @32
    wn
    @25
    @2
    @47
    vc
    cR
    @39
    @2
    @40
    @47
    @46
    @40
    @27
    cn
    wcel
    @47
    @16
    @47
    vk
    @27
    cn
    cS
    @11
    @27
    wceq
    #
    @15
    @31
    @48
    @14
    @30
    va
    vd
    cn
    cn
    @48
    @10
    vm
    @13
    @29
    @48
    @12
    @28
    cc0
    cfz
    @11
    @27
    c1
    cmin
    oveq1
    oveq2d
    raleqdv
    2rexbidv
    notbid
    vdwnn.3
    elrab2
    simprbi
    syl6
    ralimdva
    @31
    vc
    cR
    ralnex
    syl6ib
    pm2.65d
    nrexdv
    pm2.65i
end
