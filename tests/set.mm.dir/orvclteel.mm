include "cle.mm"
include "cr.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cmnf.mm"
include "cioc.mm"
include "co.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ccld.mm"
include "clt.mm"
include "wa.mm"
include "cxr.mm"
include "wcel.mm"
include "rexr.mm"
include "ad2antrl.mm"
include "mnflt.mm"
include "simprr.mm"
include "jca.mm"
include "simprl.mm"
include "adantr.mm"
include "simprrl.mm"
include "simprrr.mm"
include "xrre.mm"
include "syl22anc.mm"
include "impbida.mm"
include "rabbidva2.mm"
include "wceq.mm"
include "mnfxr.mm"
include "rexrd.mm"
include "iocval.mm"
include "sylancr.mm"
include "eqtr4d.mm"
include "iocmnfcld.mm"
include "syl.mm"
include "eqeltrd.mm"
include "orrvccel.mm"

theorem orvclteel
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cX: class X
  let vx: setvar x
  assume dstfrv.1: |- ( ph -> P e. Prob )
  assume dstfrv.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume orvclteel.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( X oRVC <_ A ) e. dom P )

  proof
    wph
    vx
    cA
    cP
    cle
    cr
    cX
    dstfrv.1
    dstfrv.2
    orvclteel.1
    wph
    vx
    cv
    #
    cA
    cle
    wbr
    #
    vx
    cr
    crab
    #
    cmnf
    cA
    cioc
    co
    #
    cioo
    crn
    ctg
    cfv
    ccld
    cfv
    #
    wph
    @2
    cmnf
    @0
    clt
    wbr
    #
    @1
    wa
    #
    vx
    cxr
    crab
    #
    @3
    wph
    @1
    @6
    vx
    cr
    cxr
    wph
    @0
    cr
    wcel
    #
    @1
    wa
    #
    @0
    cxr
    wcel
    #
    @6
    wa
    #
    wph
    @9
    wa
    #
    @10
    @6
    @8
    @10
    wph
    @1
    @0
    rexr
    ad2antrl
    @12
    @5
    @1
    @8
    @5
    wph
    @1
    @0
    mnflt
    ad2antrl
    wph
    @8
    @1
    simprr
    jca
    jca
    wph
    @11
    wa
    #
    @8
    @1
    @13
    @10
    cA
    cr
    wcel
    #
    @5
    @1
    @8
    wph
    @10
    @6
    simprl
    wph
    @14
    @11
    orvclteel.1
    adantr
    wph
    @10
    @5
    @1
    simprrl
    wph
    @10
    @5
    @1
    simprrr
    #
    @0
    cA
    xrre
    syl22anc
    @15
    jca
    impbida
    rabbidva2
    wph
    cmnf
    cxr
    wcel
    cA
    cxr
    wcel
    @3
    @7
    wceq
    mnfxr
    wph
    cA
    orvclteel.1
    rexrd
    vx
    cmnf
    cA
    iocval
    sylancr
    eqtr4d
    wph
    @14
    @3
    @4
    wcel
    orvclteel.1
    cA
    iocmnfcld
    syl
    eqeltrd
    orrvccel
end
