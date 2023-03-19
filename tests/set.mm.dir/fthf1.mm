include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wf1.mm"
include "wral.mm"
include "cfth.mm"
include "wbr.mm"
include "cfunc.mm"
include "isfth2.mm"
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
include "f1eq123d.mm"
include "rspcdv.mm"
include "rspcimdv.mm"
include "mpd.mm"

theorem fthf1
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
  assume isfth.b: |- B = ( Base ` C )
  assume isfth.h: |- H = ( Hom ` C )
  assume isfth.j: |- J = ( Hom ` D )
  assume fthf1.f: |- ( ph -> F ( C Faith D ) G )
  assume fthf1.x: |- ( ph -> X e. B )
  assume fthf1.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X G Y ) : ( X H Y ) -1-1-> ( ( F ` X ) J ( F ` Y ) ) )

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
    wf1
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
    wf1
    #
    wph
    cF
    cG
    cC
    cD
    cfth
    co
    wbr
    #
    @9
    fthf1.f
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
    isfth.b
    isfth.h
    isfth.j
    isfth2
    simprbi
    syl
    wph
    @8
    @15
    vx
    cX
    cB
    fthf1.x
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
    fthf1.y
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
    f1eq123d
    rspcdv
    rspcimdv
    mpd
end
