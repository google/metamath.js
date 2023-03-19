include "ccid.mm"
include "cfv.mm"
include "cop.mm"
include "cco.mm"
include "co.mm"
include "chom.mm"
include "eqid.mm"
include "wcel.mm"
include "wceq.mm"
include "wbr.mm"
include "w3a.mm"
include "issect.mm"
include "mpbid.mm"
include "simp1d.mm"
include "simp2d.mm"
include "catass.mm"
include "simp3d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "catlid.mm"
include "catrid.mm"

theorem sectcan
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  assume sectcan.b: |- B = ( Base ` C )
  assume sectcan.s: |- S = ( Sect ` C )
  assume sectcan.c: |- ( ph -> C e. Cat )
  assume sectcan.x: |- ( ph -> X e. B )
  assume sectcan.y: |- ( ph -> Y e. B )
  assume sectcan.1: |- ( ph -> G ( X S Y ) F )
  assume sectcan.2: |- ( ph -> F ( Y S X ) H )


  assert |- ( ph -> G = H )

  proof
    wph
    cY
    cC
    ccid
    cfv
    #
    cfv
    #
    cG
    cX
    cY
    cop
    #
    cY
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    cH
    cX
    @0
    cfv
    #
    cX
    cX
    cop
    cY
    @3
    co
    #
    co
    #
    cG
    cH
    wph
    cH
    cF
    cY
    cX
    cop
    cY
    @3
    co
    co
    #
    cG
    @4
    co
    cH
    cF
    cG
    @2
    cX
    @3
    co
    co
    #
    @7
    co
    @5
    @8
    wph
    cB
    cC
    @3
    cG
    cF
    cC
    chom
    cfv
    #
    cH
    cY
    cX
    cY
    cX
    sectcan.b
    @11
    eqid
    #
    @3
    eqid
    #
    sectcan.c
    sectcan.x
    sectcan.y
    sectcan.x
    wph
    cG
    cX
    cY
    @11
    co
    #
    wcel
    #
    cF
    cY
    cX
    @11
    co
    wcel
    #
    @10
    @6
    wceq
    #
    wph
    cG
    cF
    cX
    cY
    cS
    co
    wbr
    @15
    @16
    @17
    w3a
    sectcan.1
    wph
    cB
    cC
    cS
    @3
    @0
    cG
    cF
    @11
    cX
    cY
    sectcan.b
    @12
    @13
    @0
    eqid
    #
    sectcan.s
    sectcan.c
    sectcan.x
    sectcan.y
    issect
    mpbid
    #
    simp1d
    #
    wph
    @16
    cH
    @14
    wcel
    #
    @9
    @1
    wceq
    #
    wph
    cF
    cH
    cY
    cX
    cS
    co
    wbr
    @16
    @21
    @22
    w3a
    sectcan.2
    wph
    cB
    cC
    cS
    @3
    @0
    cF
    cH
    @11
    cY
    cX
    sectcan.b
    @12
    @13
    @18
    sectcan.s
    sectcan.c
    sectcan.y
    sectcan.x
    issect
    mpbid
    #
    simp1d
    sectcan.y
    wph
    @16
    @21
    @22
    @23
    simp2d
    #
    catass
    wph
    @9
    @1
    cG
    @4
    wph
    @16
    @21
    @22
    @23
    simp3d
    oveq1d
    wph
    @10
    @6
    cH
    @7
    wph
    @15
    @16
    @17
    @19
    simp3d
    oveq2d
    3eqtr3d
    wph
    cB
    cC
    @3
    @0
    cG
    @11
    cX
    cY
    sectcan.b
    @12
    @18
    sectcan.c
    sectcan.x
    @13
    sectcan.y
    @20
    catlid
    wph
    cB
    cC
    @3
    @0
    cH
    @11
    cX
    cY
    sectcan.b
    @12
    @18
    sectcan.c
    sectcan.x
    @13
    sectcan.y
    @24
    catrid
    3eqtr3d
end
