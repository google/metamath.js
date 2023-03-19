include "cismt.mm"
include "co.mm"
include "wcel.mm"
include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "lmif1o.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "c2.mm"
include "cstrkgld.mm"
include "wbr.mm"
include "crn.mm"
include "simprl.mm"
include "simprr.mm"
include "lmiiso.mm"
include "ralrimivva.mm"
include "wb.mm"
include "ismot.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem lmimot
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vd: setvar d
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )
  assume lmif.m: |- M = ( ( lInvG ` G ) ` D )
  assume lmif.l: |- L = ( LineG ` G )
  assume lmif.d: |- ( ph -> D e. ran L )


  assert |- ( ph -> M e. ( G Ismt G ) )

  proof
    wph
    cM
    cG
    cG
    cismt
    co
    wcel
    #
    cP
    cP
    cM
    wf1o
    #
    va
    cv
    #
    cM
    cfv
    vb
    cv
    #
    cM
    cfv
    c.mi
    co
    @2
    @3
    c.mi
    co
    wceq
    #
    vb
    cP
    wral
    va
    cP
    wral
    #
    wph
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmif.m
    lmif.l
    lmif.d
    lmif1o
    wph
    @4
    va
    vb
    cP
    cP
    wph
    @2
    cP
    wcel
    #
    @3
    cP
    wcel
    #
    wa
    #
    wa
    @2
    @3
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    ismid.p
    ismid.d
    ismid.i
    wph
    cG
    cstrkg
    wcel
    #
    @8
    ismid.g
    adantr
    wph
    cG
    c2
    cstrkgld
    wbr
    @8
    ismid.1
    adantr
    lmif.m
    lmif.l
    wph
    cD
    cL
    crn
    wcel
    @8
    lmif.d
    adantr
    wph
    @6
    @7
    simprl
    wph
    @6
    @7
    simprr
    lmiiso
    ralrimivva
    wph
    @9
    @0
    @1
    @5
    wa
    wb
    ismid.g
    cP
    cM
    cG
    c.mi
    cstrkg
    va
    vb
    ismid.p
    ismid.d
    ismot
    syl
    mpbir2and
end
