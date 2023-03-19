include "cfv.mm"
include "c2nd.mm"
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
include "simprd.mm"
include "ida2.mm"
include "oveq1d.mm"
include "chom.mm"
include "simpld.mm"
include "homahom.mm"
include "catlid.mm"
include "eqtrd.mm"
include "oteq3d.mm"
include "idahom.mm"
include "coaval.mm"
include "wceq.mm"
include "homadmcd.mm"
include "3eqtr4d.mm"

theorem arwlid
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


  assert |- ( ph -> ( ( .1. ` Y ) .x. F ) = F )

  proof
    wph
    cX
    cY
    cY
    c.1
    cfv
    #
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
    @2
    cotp
    #
    @0
    cF
    c.x
    co
    cF
    wph
    @5
    @2
    cX
    cY
    wph
    @5
    cY
    cC
    ccid
    cfv
    #
    cfv
    #
    @2
    @4
    co
    @2
    wph
    @1
    @8
    @2
    @4
    wph
    cC
    cbs
    cfv
    #
    cC
    @7
    c.1
    cY
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
    simprd
    #
    ida2
    oveq1d
    wph
    @9
    cC
    @3
    @7
    @2
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
    wph
    @14
    @15
    @16
    simpld
    @3
    eqid
    #
    @17
    wph
    @11
    @2
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
    catlid
    eqtrd
    oteq3d
    wph
    cC
    @3
    c.x
    cF
    @0
    cH
    cX
    cY
    cY
    arwlid.o
    arwlid.h
    arwlid.f
    wph
    @9
    cC
    cH
    c.1
    cY
    arwlid.a
    @10
    @12
    @17
    arwlid.h
    idahom
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
