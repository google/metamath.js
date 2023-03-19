include "co.mm"
include "c2nd.mm"
include "cfv.mm"
include "cop.mm"
include "cco.mm"
include "cotp.mm"
include "eqid.mm"
include "coaval.mm"
include "cbs.mm"
include "chom.mm"
include "wcel.mm"
include "ccat.mm"
include "homarcl.mm"
include "syl.mm"
include "wa.mm"
include "homarcl2.mm"
include "simpld.mm"
include "simprd.mm"
include "homahom.mm"
include "catcocl.mm"
include "elhomai2.mm"
include "eqeltrd.mm"

theorem coahom
  let wph: wff ph
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let c.xb: class .xb
  assume homdmcoa.o: |- .x. = ( compA ` C )
  assume homdmcoa.h: |- H = ( HomA ` C )
  assume homdmcoa.f: |- ( ph -> F e. ( X H Y ) )
  assume homdmcoa.g: |- ( ph -> G e. ( Y H Z ) )


  assert |- ( ph -> ( G .x. F ) e. ( X H Z ) )

  proof
    wph
    cG
    cF
    c.x
    co
    cX
    cZ
    cG
    c2nd
    cfv
    #
    cF
    c2nd
    cfv
    #
    cX
    cY
    cop
    cZ
    cC
    cco
    cfv
    #
    co
    co
    #
    cotp
    cX
    cZ
    cH
    co
    wph
    cC
    @2
    c.x
    cF
    cG
    cH
    cX
    cY
    cZ
    homdmcoa.o
    homdmcoa.h
    homdmcoa.f
    homdmcoa.g
    @2
    eqid
    #
    coaval
    wph
    cC
    cbs
    cfv
    #
    cC
    @3
    cH
    cC
    chom
    cfv
    #
    cX
    cZ
    homdmcoa.h
    @5
    eqid
    #
    wph
    cF
    cX
    cY
    cH
    co
    wcel
    #
    cC
    ccat
    wcel
    homdmcoa.f
    cC
    cF
    cH
    cX
    cY
    homdmcoa.h
    homarcl
    syl
    #
    @6
    eqid
    #
    wph
    cX
    @5
    wcel
    #
    cY
    @5
    wcel
    #
    wph
    @8
    @11
    @12
    wa
    homdmcoa.f
    @5
    cC
    cF
    cH
    cX
    cY
    homdmcoa.h
    @7
    homarcl2
    syl
    #
    simpld
    #
    wph
    @12
    cZ
    @5
    wcel
    #
    wph
    cG
    cY
    cZ
    cH
    co
    wcel
    #
    @12
    @15
    wa
    homdmcoa.g
    @5
    cC
    cG
    cH
    cY
    cZ
    homdmcoa.h
    @7
    homarcl2
    syl
    simprd
    #
    wph
    @5
    cC
    @2
    @1
    @0
    @6
    cX
    cY
    cZ
    @7
    @10
    @4
    @9
    @14
    wph
    @11
    @12
    @13
    simprd
    @17
    wph
    @8
    @1
    cX
    cY
    @6
    co
    wcel
    homdmcoa.f
    cC
    cF
    cH
    @6
    cX
    cY
    homdmcoa.h
    @10
    homahom
    syl
    wph
    @16
    @0
    cY
    cZ
    @6
    co
    wcel
    homdmcoa.g
    cC
    cG
    cH
    @6
    cY
    cZ
    homdmcoa.h
    @10
    homahom
    syl
    catcocl
    elhomai2
    eqeltrd
end
