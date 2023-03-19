include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "wral.mm"
include "mrissd.mm"
include "ismri2d.mm"
include "mpbid.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "sneqd.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "notbid.mm"
include "rspcdv.mm"
include "mpd.mm"

theorem ismri2dad
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume ismri2dad.1: |- N = ( mrCls ` A )
  assume ismri2dad.2: |- I = ( mrInd ` A )
  assume ismri2dad.3: |- ( ph -> A e. ( Moore ` X ) )
  assume ismri2dad.4: |- ( ph -> S e. I )
  assume ismri2dad.5: |- ( ph -> Y e. S )


  assert |- ( ph -> -. Y e. ( N ` ( S \ { Y } ) ) )

  proof
    wph
    vx
    cv
    #
    cS
    @0
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    cS
    wral
    #
    cY
    cS
    cY
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    wph
    cS
    cI
    wcel
    @6
    ismri2dad.4
    wph
    vx
    cA
    cS
    cI
    cN
    cX
    ismri2dad.1
    ismri2dad.2
    ismri2dad.3
    wph
    cA
    cS
    cI
    cX
    ismri2dad.2
    ismri2dad.3
    ismri2dad.4
    mrissd
    ismri2d
    mpbid
    wph
    @5
    @11
    vx
    cY
    cS
    ismri2dad.5
    wph
    @0
    cY
    wceq
    #
    wa
    #
    @4
    @10
    @13
    @0
    cY
    @3
    @9
    wph
    @12
    simpr
    #
    @13
    @2
    @8
    cN
    @13
    @1
    @7
    cS
    @13
    @0
    cY
    @14
    sneqd
    difeq2d
    fveq2d
    eleq12d
    notbid
    rspcdv
    mpd
end
