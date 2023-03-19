include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cvoln.mm"
include "cfv.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "cfn.mm"
include "snfi.mm"
include "a1i.mm"
include "vonmblss2.mm"
include "ssmapsn.mm"
include "eqcomd.mm"
include "eqeltrd.mm"
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
include "mpbid.mm"
include "vonvol.mm"
include "fveq2d.mm"
include "eqidd.mm"
include "3eqtr4d.mm"

theorem vonvol2
  let wph: wff ph
  let cA: class A
  let vf: setvar f
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume vonvol2.f: |- F/_ f Y
  assume vonvol2.a: |- ( ph -> A e. V )
  assume vonvol2.x: |- ( ph -> X e. dom ( voln ` { A } ) )
  assume vonvol2.y: |- Y = U_ f e. X ran f

  disjoint A f
  disjoint X f
  disjoint f ph
  disjoint k x
  assert |- ( ph -> ( ( voln ` { A } ) ` X ) = ( vol ` Y ) )

  proof
    wph
    cY
    cA
    csn
    #
    cmap
    co
    #
    @0
    cvoln
    cfv
    #
    cfv
    cY
    cvol
    cfv
    #
    cX
    @2
    cfv
    @3
    wph
    cA
    cY
    cV
    vonvol2.a
    wph
    @1
    @2
    cdm
    #
    wcel
    cY
    cvol
    cdm
    wcel
    wph
    @1
    cX
    @4
    wph
    cX
    @1
    wph
    cA
    cr
    cX
    cY
    vf
    cV
    vonvol2.f
    vonvol2.a
    wph
    @0
    cX
    @0
    cfn
    wcel
    wph
    cA
    snfi
    a1i
    vonvol2.x
    vonmblss2
    #
    vonvol2.y
    ssmapsn
    eqcomd
    #
    vonvol2.x
    eqeltrd
    wph
    cA
    cY
    cV
    vonvol2.a
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
    vonvol2.y
    wph
    @8
    cr
    wss
    #
    vf
    cX
    wral
    @9
    cr
    wss
    wph
    @10
    vf
    cX
    wph
    @7
    cX
    wcel
    #
    wa
    #
    @7
    cr
    @0
    cmap
    co
    #
    wcel
    @0
    cr
    @7
    wf
    @10
    @12
    cX
    @13
    @7
    wph
    cX
    @13
    wss
    @11
    @5
    adantr
    wph
    @11
    simpr
    sseldd
    @7
    cr
    @0
    elmapi
    @0
    cr
    @7
    frn
    3syl
    ralrimiva
    vf
    cX
    @8
    cr
    iunss
    sylibr
    syl5eqss
    vonvolmbl
    mpbid
    vonvol
    wph
    cX
    @1
    @2
    wph
    @1
    cX
    @6
    eqcomd
    fveq2d
    wph
    @3
    eqidd
    3eqtr4d
end
