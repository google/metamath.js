include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wfo.mm"
include "wral.mm"
include "cful.mm"
include "wbr.mm"
include "cfunc.mm"
include "isfull2.mm"
include "simprbi.mm"
include "syl.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "adantr.mm"
include "simplr.mm"
include "simpr.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "foeq123d.mm"
include "rspcdv.mm"
include "rspcimdv.mm"
include "mpd.mm"

theorem fullfo
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  assume isfull.b: |- B = ( Base ` C )
  assume isfull.j: |- J = ( Hom ` D )
  assume isfull.h: |- H = ( Hom ` C )
  assume fullfo.f: |- ( ph -> F ( C Full D ) G )
  assume fullfo.x: |- ( ph -> X e. B )
  assume fullfo.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X G Y ) : ( X H Y ) -onto-> ( ( F ` X ) J ( F ` Y ) ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    @0
    cF
    cfv
    #
    @1
    cF
    cfv
    #
    cJ
    co
    #
    @0
    @1
    cG
    co
    #
    wfo
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    cX
    cY
    cH
    co
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cJ
    co
    #
    cX
    cY
    cG
    co
    #
    wfo
    #
    wph
    cF
    cG
    cC
    cD
    cful
    co
    wbr
    #
    @9
    fullfo.f
    @16
    cF
    cG
    cC
    cD
    cfunc
    co
    wbr
    @9
    vx
    vy
    cB
    cC
    cD
    cF
    cG
    cH
    cJ
    isfull.b
    isfull.j
    isfull.h
    isfull2
    simprbi
    syl
    wph
    @8
    @15
    vx
    cX
    cB
    fullfo.x
    wph
    @0
    cX
    wceq
    #
    wa
    #
    @7
    @15
    vy
    cY
    cB
    wph
    cY
    cB
    wcel
    @17
    fullfo.y
    adantr
    @18
    @1
    cY
    wceq
    #
    wa
    #
    @2
    @10
    @5
    @13
    @6
    @14
    @20
    @0
    cX
    @1
    cY
    cG
    wph
    @17
    @19
    simplr
    #
    @18
    @19
    simpr
    #
    oveq12d
    @20
    @0
    cX
    @1
    cY
    cH
    @21
    @22
    oveq12d
    @20
    @3
    @11
    @4
    @12
    cJ
    @20
    @0
    cX
    cF
    @21
    fveq2d
    @20
    @1
    cY
    cF
    @22
    fveq2d
    oveq12d
    foeq123d
    rspcdv
    rspcimdv
    mpd
end
