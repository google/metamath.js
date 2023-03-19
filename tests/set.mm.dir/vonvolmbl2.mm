include "csn.mm"
include "cvoln.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "cvol.mm"
include "cr.mm"
include "ssmapsn.mm"
include "eleq1d.mm"
include "cv.mm"
include "crn.mm"
include "ciun.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "elmapi.mm"
include "frn.mm"
include "3syl.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "vonvolmbl.mm"
include "bitrd.mm"

theorem vonvolmbl2
  let wph: wff ph
  let cA: class A
  let vf: setvar f
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume vonvolmbl2.f: |- F/_ f Y
  assume vonvolmbl2.a: |- ( ph -> A e. V )
  assume vonvolmbl2.x: |- ( ph -> X C_ ( RR ^m { A } ) )
  assume vonvolmbl2.y: |- Y = U_ f e. X ran f

  disjoint A f
  disjoint X f
  disjoint f ph
  disjoint k x
  assert |- ( ph -> ( X e. dom ( voln ` { A } ) <-> Y e. dom vol ) )

  proof
    wph
    cX
    cA
    csn
    #
    cvoln
    cfv
    cdm
    #
    wcel
    cY
    @0
    cmap
    co
    #
    @1
    wcel
    cY
    cvol
    cdm
    wcel
    wph
    cX
    @2
    @1
    wph
    cA
    cr
    cX
    cY
    vf
    cV
    vonvolmbl2.f
    vonvolmbl2.a
    vonvolmbl2.x
    vonvolmbl2.y
    ssmapsn
    eleq1d
    wph
    cA
    cY
    cV
    vonvolmbl2.a
    wph
    cY
    vf
    cX
    vf
    cv
    #
    crn
    #
    ciun
    #
    cr
    vonvolmbl2.y
    wph
    @4
    cr
    wss
    #
    vf
    cX
    wral
    @5
    cr
    wss
    wph
    @6
    vf
    cX
    wph
    @3
    cX
    wcel
    #
    wa
    #
    @3
    cr
    @0
    cmap
    co
    #
    wcel
    @0
    cr
    @3
    wf
    @6
    @8
    cX
    @9
    @3
    wph
    cX
    @9
    wss
    @7
    vonvolmbl2.x
    adantr
    wph
    @7
    simpr
    sseldd
    @3
    cr
    @0
    elmapi
    @0
    cr
    @3
    frn
    3syl
    ralrimiva
    vf
    cX
    @4
    cr
    iunss
    sylibr
    syl5eqss
    vonvolmbl
    bitrd
end
