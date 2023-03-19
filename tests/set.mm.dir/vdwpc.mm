include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "cvv.mm"
include "cop.mm"
include "cvdwp.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cvdwa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wral.mm"
include "cmpt.mm"
include "crn.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cmap.mm"
include "wrex.mm"
include "wb.mm"
include "wf.mm"
include "fex.mm"
include "sylancl.mm"
include "c1.mm"
include "cfz.mm"
include "coprab.mm"
include "w3a.mm"
include "df-br.mm"
include "df-vdwpc.mm"
include "eleq2i.mm"
include "bitri.mm"
include "simp1.mm"
include "oveq2d.mm"
include "syl6eqr.mm"
include "simp2.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "simp3.mm"
include "cnveqd.mm"
include "fveq1d.mm"
include "sneqd.mm"
include "imaeq12d.mm"
include "sseq12d.mm"
include "raleqbidv.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "rexbidv.mm"
include "eloprabga.mm"
include "syl5bb.mm"
include "syl3anc.mm"

theorem vdwpc
  let wph: wff ph
  let cR: class R
  let vi: setvar i
  let cF: class F
  let cJ: class J
  let cK: class K
  let cM: class M
  let cX: class X
  let va: setvar a
  let vd: setvar d
  let vc: setvar c
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  assume vdwmc.1: |- X e. _V
  assume vdwmc.2: |- ( ph -> K e. NN0 )
  assume vdwmc.3: |- ( ph -> F : X --> R )
  assume vdwpc.4: |- ( ph -> M e. NN )
  assume vdwpc.5: |- J = ( 1 ... M )

  disjoint a d
  disjoint a i
  disjoint F a
  disjoint d i
  disjoint F d
  disjoint F i
  disjoint K a
  disjoint K d
  disjoint K i
  disjoint J d
  disjoint J i
  disjoint M a
  disjoint M d
  disjoint M i
  disjoint a c
  disjoint a f
  disjoint a k
  disjoint a m
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint c d
  disjoint c f
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c w
  disjoint c x
  disjoint c z
  disjoint F c
  disjoint d f
  disjoint d k
  disjoint d m
  disjoint d w
  disjoint d x
  disjoint d z
  disjoint f i
  disjoint f k
  disjoint f m
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint F f
  disjoint i k
  disjoint i m
  disjoint i w
  disjoint i x
  disjoint i z
  disjoint k m
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint m w
  disjoint m x
  disjoint m z
  disjoint F m
  disjoint w x
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint K c
  disjoint K f
  disjoint K k
  disjoint K m
  disjoint K w
  disjoint K x
  disjoint K z
  disjoint c ph
  disjoint ph x
  disjoint J f
  disjoint J k
  disjoint J m
  disjoint M f
  disjoint M k
  disjoint M m
  assert |- ( ph -> ( <. M , K >. PolyAP F <-> E. a e. NN E. d e. ( NN ^m J ) ( A. i e. J ( ( a + ( d ` i ) ) ( AP ` K ) ( d ` i ) ) C_ ( `' F " { ( F ` ( a + ( d ` i ) ) ) } ) /\ ( # ` ran ( i e. J |-> ( F ` ( a + ( d ` i ) ) ) ) ) = M ) ) )

  proof
    wph
    cM
    cn
    wcel
    #
    cK
    cn0
    wcel
    #
    cF
    cvv
    wcel
    #
    cM
    cK
    cop
    #
    cF
    cvdwp
    wbr
    #
    va
    cv
    vi
    cv
    vd
    cv
    cfv
    #
    caddc
    co
    #
    @5
    cK
    cvdwa
    cfv
    #
    co
    #
    cF
    ccnv
    #
    @6
    cF
    cfv
    #
    csn
    #
    cima
    #
    wss
    #
    vi
    cJ
    wral
    #
    vi
    cJ
    @10
    cmpt
    #
    crn
    #
    chash
    cfv
    #
    cM
    wceq
    #
    wa
    #
    vd
    cn
    cJ
    cmap
    co
    #
    wrex
    #
    va
    cn
    wrex
    #
    wb
    vdwpc.4
    vdwmc.2
    wph
    cX
    cR
    cF
    wf
    cX
    cvv
    wcel
    @2
    vdwmc.3
    vdwmc.1
    cX
    cR
    cvv
    cF
    fex
    sylancl
    @4
    @3
    cF
    cop
    #
    @6
    @5
    vk
    cv
    #
    cvdwa
    cfv
    #
    co
    #
    vf
    cv
    #
    ccnv
    #
    @6
    @27
    cfv
    #
    csn
    #
    cima
    #
    wss
    #
    vi
    c1
    vm
    cv
    #
    cfz
    co
    #
    wral
    #
    vi
    @34
    @29
    cmpt
    #
    crn
    #
    chash
    cfv
    #
    @33
    wceq
    #
    wa
    #
    vd
    cn
    @34
    cmap
    co
    #
    wrex
    #
    va
    cn
    wrex
    #
    vm
    vk
    vf
    coprab
    #
    wcel
    #
    @0
    @1
    @2
    w3a
    @22
    @4
    @23
    cvdwp
    wcel
    @45
    @3
    cF
    cvdwp
    df-br
    cvdwp
    @44
    @23
    vf
    vi
    vk
    vm
    va
    vd
    df-vdwpc
    eleq2i
    bitri
    @43
    @22
    vm
    vk
    vf
    cM
    cK
    cF
    cn
    cn0
    cvv
    @33
    cM
    wceq
    #
    @24
    cK
    wceq
    #
    @27
    cF
    wceq
    #
    w3a
    #
    @42
    @21
    va
    cn
    @49
    @40
    @19
    vd
    @41
    @20
    @49
    @34
    cJ
    cn
    cmap
    @49
    @34
    c1
    cM
    cfz
    co
    cJ
    @49
    @33
    cM
    c1
    cfz
    @46
    @47
    @48
    simp1
    #
    oveq2d
    vdwpc.5
    syl6eqr
    #
    oveq2d
    @49
    @35
    @14
    @39
    @18
    @49
    @32
    @13
    vi
    @34
    cJ
    @51
    @49
    @26
    @8
    @31
    @12
    @49
    @25
    @7
    @6
    @5
    @49
    @24
    cK
    cvdwa
    @46
    @47
    @48
    simp2
    fveq2d
    oveqd
    @49
    @28
    @9
    @30
    @11
    @49
    @27
    cF
    @46
    @47
    @48
    simp3
    #
    cnveqd
    @49
    @29
    @10
    @49
    @6
    @27
    cF
    @52
    fveq1d
    #
    sneqd
    imaeq12d
    sseq12d
    raleqbidv
    @49
    @38
    @17
    @33
    cM
    @49
    @37
    @16
    chash
    @49
    @36
    @15
    @49
    vi
    @34
    @29
    cJ
    @10
    @51
    @53
    mpteq12dv
    rneqd
    fveq2d
    @50
    eqeq12d
    anbi12d
    rexeqbidv
    rexbidv
    eloprabga
    syl5bb
    syl3anc
end
