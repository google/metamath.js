include "cop.mm"
include "co.mm"
include "wbr.mm"
include "ccid.mm"
include "cfv.mm"
include "wceq.mm"
include "chom.mm"
include "eqid.mm"
include "wcel.mm"
include "w3a.mm"
include "issect.mm"
include "mpbid.mm"
include "simp1d.mm"
include "catcocl.mm"
include "simp2d.mm"
include "catass.mm"
include "simp3d.mm"
include "oveq1d.mm"
include "catlid.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "issect2.mm"
include "mpbird.mm"

theorem sectco
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume sectco.b: |- B = ( Base ` C )
  assume sectco.o: |- .x. = ( comp ` C )
  assume sectco.s: |- S = ( Sect ` C )
  assume sectco.c: |- ( ph -> C e. Cat )
  assume sectco.x: |- ( ph -> X e. B )
  assume sectco.y: |- ( ph -> Y e. B )
  assume sectco.z: |- ( ph -> Z e. B )
  assume sectco.1: |- ( ph -> F ( X S Y ) G )
  assume sectco.2: |- ( ph -> H ( Y S Z ) K )


  assert |- ( ph -> ( H ( <. X , Y >. .x. Z ) F ) ( X S Z ) ( G ( <. Z , Y >. .x. X ) K ) )

  proof
    wph
    cH
    cF
    cX
    cY
    cop
    #
    cZ
    c.x
    co
    co
    #
    cG
    cK
    cZ
    cY
    cop
    cX
    c.x
    co
    co
    #
    cX
    cZ
    cS
    co
    wbr
    @2
    @1
    cX
    cZ
    cop
    #
    cX
    c.x
    co
    co
    #
    cX
    cC
    ccid
    cfv
    #
    cfv
    #
    wceq
    wph
    @4
    cG
    cK
    @1
    @3
    cY
    c.x
    co
    co
    #
    @0
    cX
    c.x
    co
    #
    co
    cG
    cF
    @8
    co
    #
    @6
    wph
    cB
    cC
    c.x
    @1
    cK
    cC
    chom
    cfv
    #
    cG
    cX
    cX
    cZ
    cY
    sectco.b
    @10
    eqid
    #
    sectco.o
    sectco.c
    sectco.x
    sectco.z
    sectco.y
    wph
    cB
    cC
    c.x
    cF
    cH
    @10
    cX
    cY
    cZ
    sectco.b
    @11
    sectco.o
    sectco.c
    sectco.x
    sectco.y
    sectco.z
    wph
    cF
    cX
    cY
    @10
    co
    wcel
    #
    cG
    cY
    cX
    @10
    co
    wcel
    #
    @9
    @6
    wceq
    #
    wph
    cF
    cG
    cX
    cY
    cS
    co
    wbr
    @12
    @13
    @14
    w3a
    sectco.1
    wph
    cB
    cC
    cS
    c.x
    @5
    cF
    cG
    @10
    cX
    cY
    sectco.b
    @11
    sectco.o
    @5
    eqid
    #
    sectco.s
    sectco.c
    sectco.x
    sectco.y
    issect
    mpbid
    #
    simp1d
    #
    wph
    cH
    cY
    cZ
    @10
    co
    wcel
    #
    cK
    cZ
    cY
    @10
    co
    wcel
    #
    cK
    cH
    cY
    cZ
    cop
    cY
    c.x
    co
    co
    #
    cY
    @5
    cfv
    #
    wceq
    #
    wph
    cH
    cK
    cY
    cZ
    cS
    co
    wbr
    @18
    @19
    @22
    w3a
    sectco.2
    wph
    cB
    cC
    cS
    c.x
    @5
    cH
    cK
    @10
    cY
    cZ
    sectco.b
    @11
    sectco.o
    @15
    sectco.s
    sectco.c
    sectco.y
    sectco.z
    issect
    mpbid
    #
    simp1d
    #
    catcocl
    #
    wph
    @18
    @19
    @22
    @23
    simp2d
    #
    sectco.x
    wph
    @12
    @13
    @14
    @16
    simp2d
    #
    catass
    wph
    @7
    cF
    cG
    @8
    wph
    @20
    cF
    @0
    cY
    c.x
    co
    #
    co
    @21
    cF
    @28
    co
    @7
    cF
    wph
    @20
    @21
    cF
    @28
    wph
    @18
    @19
    @22
    @23
    simp3d
    oveq1d
    wph
    cB
    cC
    c.x
    cF
    cH
    @10
    cK
    cY
    cX
    cY
    cZ
    sectco.b
    @11
    sectco.o
    sectco.c
    sectco.x
    sectco.y
    sectco.z
    @17
    @24
    sectco.y
    @26
    catass
    wph
    cB
    cC
    c.x
    @5
    cF
    @10
    cX
    cY
    sectco.b
    @11
    @15
    sectco.c
    sectco.x
    sectco.o
    sectco.y
    @17
    catlid
    3eqtr3d
    oveq2d
    wph
    @12
    @13
    @14
    @16
    simp3d
    3eqtrd
    wph
    cB
    cC
    cS
    c.x
    @5
    @1
    @2
    @10
    cX
    cZ
    sectco.b
    @11
    sectco.o
    @15
    sectco.s
    sectco.c
    sectco.x
    sectco.z
    @25
    wph
    cB
    cC
    c.x
    cK
    cG
    @10
    cZ
    cY
    cX
    sectco.b
    @11
    sectco.o
    sectco.c
    sectco.z
    sectco.y
    sectco.x
    @26
    @27
    catcocl
    issect2
    mpbird
end
