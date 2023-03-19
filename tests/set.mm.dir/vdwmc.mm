include "cvdwm.mm"
include "wbr.mm"
include "cvdwa.mm"
include "cfv.mm"
include "crn.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cpw.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "co.mm"
include "wss.mm"
include "cn.mm"
include "wrex.mm"
include "cn0.mm"
include "wcel.mm"
include "cvv.mm"
include "wb.mm"
include "wf.mm"
include "fex.mm"
include "sylancl.mm"
include "wceq.mm"
include "wa.mm"
include "fveq2.mm"
include "rneqd.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "pweqd.mm"
include "ineqan12d.mm"
include "neeq1d.mm"
include "exbidv.mm"
include "df-vdwmc.mm"
include "brabga.mm"
include "syl2anc.mm"
include "cxp.mm"
include "wfn.mm"
include "vdwapf.mm"
include "ffn.mm"
include "selpw.mm"
include "sseq1.mm"
include "syl5bb.mm"
include "rexrn.mm"
include "4syl.mm"
include "elin.mm"
include "exbii.mm"
include "n0.mm"
include "df-rex.mm"
include "3bitr4ri.mm"
include "cop.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "sseq1d.mm"
include "rexxp.mm"
include "3bitr3g.mm"
include "bitrd.mm"

theorem vdwmc
  let wph: wff ph
  let cR: class R
  let cF: class F
  let cK: class K
  let cX: class X
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let cJ: class J
  let cM: class M
  assume vdwmc.1: |- X e. _V
  assume vdwmc.2: |- ( ph -> K e. NN0 )
  assume vdwmc.3: |- ( ph -> F : X --> R )

  disjoint a c
  disjoint a d
  disjoint F a
  disjoint c d
  disjoint F c
  disjoint F d
  disjoint K a
  disjoint K c
  disjoint K d
  disjoint c ph
  disjoint a f
  disjoint a i
  disjoint a k
  disjoint a m
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint c f
  disjoint c i
  disjoint c k
  disjoint c m
  disjoint c w
  disjoint c x
  disjoint c z
  disjoint d f
  disjoint d i
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
  disjoint F i
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
  disjoint K f
  disjoint K i
  disjoint K k
  disjoint K m
  disjoint K w
  disjoint K x
  disjoint K z
  disjoint ph x
  disjoint J d
  disjoint J f
  disjoint J i
  disjoint J k
  disjoint J m
  disjoint M a
  disjoint M d
  disjoint M f
  disjoint M i
  disjoint M k
  disjoint M m
  assert |- ( ph -> ( K MonoAP F <-> E. c E. a e. NN E. d e. NN ( a ( AP ` K ) d ) C_ ( `' F " { c } ) ) )

  proof
    wph
    cK
    cF
    cvdwm
    wbr
    #
    cK
    cvdwa
    cfv
    #
    crn
    #
    cF
    ccnv
    #
    vc
    cv
    csn
    #
    cima
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vc
    wex
    #
    va
    cv
    #
    vd
    cv
    #
    @1
    co
    #
    @5
    wss
    #
    vd
    cn
    wrex
    va
    cn
    wrex
    #
    vc
    wex
    wph
    cK
    cn0
    wcel
    #
    cF
    cvv
    wcel
    #
    @0
    @9
    wb
    vdwmc.2
    wph
    cX
    cR
    cF
    wf
    cX
    cvv
    wcel
    @16
    vdwmc.3
    vdwmc.1
    cX
    cR
    cvv
    cF
    fex
    sylancl
    vk
    cv
    #
    cvdwa
    cfv
    #
    crn
    #
    vf
    cv
    #
    ccnv
    #
    @4
    cima
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vc
    wex
    @9
    vk
    vf
    cK
    cF
    cvdwm
    cn0
    cvv
    @17
    cK
    wceq
    #
    @20
    cF
    wceq
    #
    wa
    #
    @25
    @8
    vc
    @28
    @24
    @7
    c0
    @26
    @27
    @19
    @2
    @23
    @6
    @26
    @18
    @1
    @17
    cK
    cvdwa
    fveq2
    rneqd
    @27
    @22
    @5
    @27
    @21
    @3
    @4
    @20
    cF
    cnveq
    imaeq1d
    pweqd
    ineqan12d
    neeq1d
    exbidv
    vf
    vk
    vc
    df-vdwmc
    brabga
    syl2anc
    wph
    @8
    @14
    vc
    wph
    vz
    cv
    #
    @6
    wcel
    #
    vz
    @2
    wrex
    #
    vw
    cv
    #
    @1
    cfv
    #
    @5
    wss
    #
    vw
    cn
    cn
    cxp
    #
    wrex
    #
    @8
    @14
    wph
    @15
    @35
    cn
    cpw
    #
    @1
    wf
    @1
    @35
    wfn
    @31
    @36
    wb
    vdwmc.2
    cK
    vdwapf
    @35
    @37
    @1
    ffn
    @30
    @34
    vz
    vw
    @35
    @1
    @30
    @29
    @5
    wss
    @29
    @33
    wceq
    @34
    vz
    @5
    selpw
    @29
    @33
    @5
    sseq1
    syl5bb
    rexrn
    4syl
    @29
    @7
    wcel
    #
    vz
    wex
    @29
    @2
    wcel
    @30
    wa
    #
    vz
    wex
    @8
    @31
    @38
    @39
    vz
    @29
    @2
    @6
    elin
    exbii
    vz
    @7
    n0
    @30
    vz
    @2
    df-rex
    3bitr4ri
    @34
    @13
    vw
    va
    vd
    cn
    cn
    @32
    @10
    @11
    cop
    #
    wceq
    #
    @33
    @12
    @5
    @41
    @33
    @40
    @1
    cfv
    @12
    @32
    @40
    @1
    fveq2
    @10
    @11
    @1
    df-ov
    syl6eqr
    sseq1d
    rexxp
    3bitr3g
    exbidv
    bitrd
end
