include "carw.mm"
include "cfv.mm"
include "wcel.mm"
include "ccoda.mm"
include "cdoma.mm"
include "wceq.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "eqid.mm"
include "homarw.mm"
include "sseldi.mm"
include "homacd.mm"
include "syl.mm"
include "homadm.mm"
include "eqtr4d.mm"
include "eldmcoa.mm"
include "syl3anbrc.mm"

theorem homdmcoa
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


  assert |- ( ph -> G dom .x. F )

  proof
    wph
    cF
    cC
    carw
    cfv
    #
    wcel
    cG
    @0
    wcel
    cF
    ccoda
    cfv
    #
    cG
    cdoma
    cfv
    #
    wceq
    cG
    cF
    c.x
    cdm
    wbr
    wph
    cX
    cY
    cH
    co
    #
    @0
    cF
    @0
    cC
    cH
    cX
    cY
    @0
    eqid
    #
    homdmcoa.h
    homarw
    homdmcoa.f
    sseldi
    wph
    cY
    cZ
    cH
    co
    #
    @0
    cG
    @0
    cC
    cH
    cY
    cZ
    @4
    homdmcoa.h
    homarw
    homdmcoa.g
    sseldi
    wph
    @1
    cY
    @2
    wph
    cF
    @3
    wcel
    @1
    cY
    wceq
    homdmcoa.f
    cC
    cF
    cH
    cX
    cY
    homdmcoa.h
    homacd
    syl
    wph
    cG
    @5
    wcel
    @2
    cY
    wceq
    homdmcoa.g
    cC
    cG
    cH
    cY
    cZ
    homdmcoa.h
    homadm
    syl
    eqtr4d
    @0
    cC
    c.x
    cF
    cG
    homdmcoa.o
    @4
    eldmcoa
    syl3anbrc
end
