include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "csca.mm"
include "cbs.mm"
include "wrex.mm"
include "cab.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cof.mm"
include "wss.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "clvec.mm"
include "eqid.mm"
include "ldualsbase.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "adantr.mm"
include "simpr.mm"
include "ldualvs.mm"
include "eqeq2d.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "rexbidv2.mm"
include "abbidv.mm"
include "clmod.mm"
include "lveclmod.mm"
include "lduallmod.mm"
include "syl.mm"
include "ldualelvbase.mm"
include "lspsn.mm"
include "syl2anc.mm"
include "lfl1dim.mm"
include "3eqtr4d.mm"

theorem ldual1dim
  let wph: wff ph
  let cD: class D
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cL: class L
  let cN: class N
  let cW: class W
  let vk: setvar k
  assume ldual1dim.f: |- F = ( LFnl ` W )
  assume ldual1dim.l: |- L = ( LKer ` W )
  assume ldual1dim.d: |- D = ( LDual ` W )
  assume ldual1dim.n: |- N = ( LSpan ` D )
  assume ldual1dim.w: |- ( ph -> W e. LVec )
  assume ldual1dim.g: |- ( ph -> G e. F )

  disjoint D g
  disjoint G g
  disjoint N g
  disjoint g ph
  disjoint g k
  disjoint D k
  disjoint F k
  disjoint G k
  disjoint L k
  disjoint N k
  disjoint W k
  disjoint k ph
  assert |- ( ph -> ( N ` { G } ) = { g e. F | ( L ` G ) C_ ( L ` g ) } )

  proof
    wph
    vg
    cv
    #
    vk
    cv
    #
    cG
    cD
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vk
    cD
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    vg
    cab
    #
    @0
    cG
    cW
    cbs
    cfv
    #
    @1
    csn
    cxp
    cW
    csca
    cfv
    #
    cmulr
    cfv
    #
    cof
    co
    #
    wceq
    #
    vk
    @10
    cbs
    cfv
    #
    wrex
    #
    vg
    cab
    cG
    csn
    cN
    cfv
    #
    cG
    cL
    cfv
    @0
    cL
    cfv
    wss
    vg
    cF
    crab
    wph
    @7
    @15
    vg
    wph
    @4
    @13
    vk
    @6
    @14
    wph
    @1
    @6
    wcel
    #
    @4
    wa
    @1
    @14
    wcel
    #
    @4
    wa
    @18
    @13
    wa
    wph
    @17
    @18
    @4
    wph
    @6
    @14
    @1
    wph
    cD
    @5
    @10
    @6
    @14
    clvec
    cW
    @10
    eqid
    #
    @14
    eqid
    #
    ldual1dim.d
    @5
    eqid
    #
    @6
    eqid
    #
    ldual1dim.w
    ldualsbase
    eleq2d
    anbi1d
    wph
    @18
    @4
    @13
    wph
    @18
    wa
    #
    @3
    @12
    @0
    @23
    cD
    @10
    @2
    @11
    cF
    cG
    @14
    @9
    cW
    @1
    clvec
    ldual1dim.f
    @9
    eqid
    #
    @19
    @20
    @11
    eqid
    #
    ldual1dim.d
    @2
    eqid
    #
    wph
    cW
    clvec
    wcel
    #
    @18
    ldual1dim.w
    adantr
    wph
    @18
    simpr
    wph
    cG
    cF
    wcel
    @18
    ldual1dim.g
    adantr
    ldualvs
    eqeq2d
    pm5.32da
    bitrd
    rexbidv2
    abbidv
    wph
    cD
    clmod
    wcel
    #
    cG
    cD
    cbs
    cfv
    #
    wcel
    @16
    @8
    wceq
    wph
    @27
    @28
    ldual1dim.w
    @27
    cD
    cW
    ldual1dim.d
    cW
    lveclmod
    lduallmod
    syl
    wph
    cD
    cF
    cG
    @29
    cW
    clvec
    ldual1dim.f
    ldual1dim.d
    @29
    eqid
    #
    ldual1dim.w
    ldual1dim.g
    ldualelvbase
    vg
    @2
    vk
    @5
    @6
    cN
    @29
    cD
    cG
    @21
    @22
    @30
    @26
    ldual1dim.n
    lspsn
    syl2anc
    wph
    @10
    @11
    vg
    vk
    cF
    cG
    @14
    cL
    @9
    cW
    @24
    @19
    ldual1dim.f
    ldual1dim.l
    @20
    @25
    ldual1dim.w
    ldual1dim.g
    lfl1dim
    3eqtr4d
end
