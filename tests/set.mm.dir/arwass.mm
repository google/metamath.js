include "co.mm"
include "c2nd.mm"
include "cfv.mm"
include "cop.mm"
include "cco.mm"
include "cotp.mm"
include "cbs.mm"
include "chom.mm"
include "eqid.mm"
include "wcel.mm"
include "ccat.mm"
include "homarcl.mm"
include "syl.mm"
include "wa.mm"
include "homarcl2.mm"
include "simpld.mm"
include "simprd.mm"
include "homahom.mm"
include "catass.mm"
include "coa2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "oteq3d.mm"
include "coahom.mm"
include "coaval.mm"

theorem arwass
  let wph: wff ph
  let cC: class C
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume arwlid.h: |- H = ( HomA ` C )
  assume arwlid.o: |- .x. = ( compA ` C )
  assume arwlid.a: |- .1. = ( IdA ` C )
  assume arwlid.f: |- ( ph -> F e. ( X H Y ) )
  assume arwass.g: |- ( ph -> G e. ( Y H Z ) )
  assume arwass.k: |- ( ph -> K e. ( Z H W ) )


  assert |- ( ph -> ( ( K .x. G ) .x. F ) = ( K .x. ( G .x. F ) ) )

  proof
    wph
    cX
    cW
    cK
    cG
    c.x
    co
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
    #
    cW
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
    cW
    cK
    c2nd
    cfv
    #
    cG
    cF
    c.x
    co
    #
    c2nd
    cfv
    #
    cX
    cZ
    cop
    cW
    @4
    co
    #
    co
    #
    cotp
    @0
    cF
    c.x
    co
    cK
    @8
    c.x
    co
    wph
    @6
    @11
    cX
    cW
    wph
    @7
    cG
    c2nd
    cfv
    #
    cY
    cZ
    cop
    cW
    @4
    co
    co
    #
    @2
    @5
    co
    @7
    @12
    @2
    @3
    cZ
    @4
    co
    co
    #
    @10
    co
    @6
    @11
    wph
    cC
    cbs
    cfv
    #
    cC
    @4
    @2
    @12
    cC
    chom
    cfv
    #
    @7
    cW
    cX
    cY
    cZ
    @15
    eqid
    #
    @16
    eqid
    #
    @4
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
    wph
    cX
    @15
    wcel
    #
    cY
    @15
    wcel
    #
    wph
    @20
    @21
    @22
    wa
    arwlid.f
    @15
    cC
    cF
    cH
    cX
    cY
    arwlid.h
    @17
    homarcl2
    syl
    #
    simpld
    wph
    @21
    @22
    @23
    simprd
    wph
    cZ
    @15
    wcel
    #
    cW
    @15
    wcel
    #
    wph
    cK
    cZ
    cW
    cH
    co
    wcel
    #
    @24
    @25
    wa
    arwass.k
    @15
    cC
    cK
    cH
    cZ
    cW
    arwlid.h
    @17
    homarcl2
    syl
    #
    simpld
    wph
    @20
    @2
    cX
    cY
    @16
    co
    wcel
    arwlid.f
    cC
    cF
    cH
    @16
    cX
    cY
    arwlid.h
    @18
    homahom
    syl
    wph
    cG
    cY
    cZ
    cH
    co
    wcel
    @12
    cY
    cZ
    @16
    co
    wcel
    arwass.g
    cC
    cG
    cH
    @16
    cY
    cZ
    arwlid.h
    @18
    homahom
    syl
    wph
    @24
    @25
    @27
    simprd
    wph
    @26
    @7
    cZ
    cW
    @16
    co
    wcel
    arwass.k
    cC
    cK
    cH
    @16
    cZ
    cW
    arwlid.h
    @18
    homahom
    syl
    catass
    wph
    @1
    @13
    @2
    @5
    wph
    cC
    @4
    c.x
    cG
    cK
    cH
    cY
    cZ
    cW
    arwlid.o
    arwlid.h
    arwass.g
    arwass.k
    @19
    coa2
    oveq1d
    wph
    @9
    @14
    @7
    @10
    wph
    cC
    @4
    c.x
    cF
    cG
    cH
    cX
    cY
    cZ
    arwlid.o
    arwlid.h
    arwlid.f
    arwass.g
    @19
    coa2
    oveq2d
    3eqtr4d
    oteq3d
    wph
    cC
    @4
    c.x
    cF
    @0
    cH
    cX
    cY
    cW
    arwlid.o
    arwlid.h
    arwlid.f
    wph
    cC
    c.x
    cG
    cK
    cH
    cY
    cZ
    cW
    arwlid.o
    arwlid.h
    arwass.g
    arwass.k
    coahom
    @19
    coaval
    wph
    cC
    @4
    c.x
    @8
    cK
    cH
    cX
    cZ
    cW
    arwlid.o
    arwlid.h
    wph
    cC
    c.x
    cF
    cG
    cH
    cX
    cY
    cZ
    arwlid.o
    arwlid.h
    arwlid.f
    arwass.g
    coahom
    arwass.k
    @19
    coaval
    3eqtr4d
end
