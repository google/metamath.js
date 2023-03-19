include "c2nd.mm"
include "cfv.mm"
include "cop.mm"
include "cco.mm"
include "co.mm"
include "cotp.mm"
include "ccid.mm"
include "cbs.mm"
include "eqid.mm"
include "wcel.mm"
include "ccat.mm"
include "homarcl.mm"
include "syl.mm"
include "wa.mm"
include "homarcl2.mm"
include "simpld.mm"
include "ida2.mm"
include "oveq2d.mm"
include "chom.mm"
include "simprd.mm"
include "homahom.mm"
include "catrid.mm"
include "eqtrd.mm"
include "oteq3d.mm"
include "idahom.mm"
include "coaval.mm"
include "wceq.mm"
include "homadmcd.mm"
include "3eqtr4d.mm"

theorem arwrid
  let wph: wff ph
  let cC: class C
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cH: class H
  let cX: class X
  let cY: class Y
  assume arwlid.h: |- H = ( HomA ` C )
  assume arwlid.o: |- .x. = ( compA ` C )
  assume arwlid.a: |- .1. = ( IdA ` C )
  assume arwlid.f: |- ( ph -> F e. ( X H Y ) )


  assert |- ( ph -> ( F .x. ( .1. ` X ) ) = F )

  proof
    wph
    cX
    cY
    cF
    c2nd
    cfv
    #
    cX
    c.1
    cfv
    #
    c2nd
    cfv
    #
    cX
    cX
    cop
    cY
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    cotp
    cX
    cY
    @0
    cotp
    #
    cF
    @1
    c.x
    co
    cF
    wph
    @5
    @0
    cX
    cY
    wph
    @5
    @0
    cX
    cC
    ccid
    cfv
    #
    cfv
    #
    @4
    co
    @0
    wph
    @2
    @8
    @0
    @4
    wph
    cC
    cbs
    cfv
    #
    cC
    @7
    c.1
    cX
    arwlid.a
    @9
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
    arwlid.f
    cC
    cF
    cH
    cX
    cY
    arwlid.h
    homarcl
    syl
    #
    @7
    eqid
    #
    wph
    cX
    @9
    wcel
    #
    cY
    @9
    wcel
    #
    wph
    @11
    @14
    @15
    wa
    arwlid.f
    @9
    cC
    cF
    cH
    cX
    cY
    arwlid.h
    @10
    homarcl2
    syl
    #
    simpld
    #
    ida2
    oveq2d
    wph
    @9
    cC
    @3
    @7
    @0
    cC
    chom
    cfv
    #
    cX
    cY
    @10
    @18
    eqid
    #
    @13
    @12
    @17
    @3
    eqid
    #
    wph
    @14
    @15
    @16
    simprd
    wph
    @11
    @0
    cX
    cY
    @18
    co
    wcel
    arwlid.f
    cC
    cF
    cH
    @18
    cX
    cY
    arwlid.h
    @19
    homahom
    syl
    catrid
    eqtrd
    oteq3d
    wph
    cC
    @3
    c.x
    @1
    cF
    cH
    cX
    cX
    cY
    arwlid.o
    arwlid.h
    wph
    @9
    cC
    cH
    c.1
    cX
    arwlid.a
    @10
    @12
    @17
    arwlid.h
    idahom
    arwlid.f
    @20
    coaval
    wph
    @11
    cF
    @6
    wceq
    arwlid.f
    cC
    cF
    cH
    cX
    cY
    arwlid.h
    homadmcd
    syl
    3eqtr4d
end
