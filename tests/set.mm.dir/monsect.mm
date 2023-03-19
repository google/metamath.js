include "co.mm"
include "wbr.mm"
include "cop.mm"
include "cco.mm"
include "cfv.mm"
include "ccid.mm"
include "wceq.mm"
include "chom.mm"
include "wcel.mm"
include "w3a.mm"
include "eqid.mm"
include "issect.mm"
include "mpbid.mm"
include "simp3d.mm"
include "oveq1d.mm"
include "simp2d.mm"
include "simp1d.mm"
include "catass.mm"
include "catlid.mm"
include "catrid.mm"
include "eqtr4d.mm"
include "3eqtr3d.mm"
include "catcocl.mm"
include "catidcl.mm"
include "moni.mm"
include "issect2.mm"
include "mpbird.mm"
include "isinv.mm"
include "mpbir2and.mm"

theorem monsect
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  assume sectmon.b: |- B = ( Base ` C )
  assume sectmon.m: |- M = ( Mono ` C )
  assume sectmon.s: |- S = ( Sect ` C )
  assume sectmon.c: |- ( ph -> C e. Cat )
  assume sectmon.x: |- ( ph -> X e. B )
  assume sectmon.y: |- ( ph -> Y e. B )
  assume monsect.n: |- N = ( Inv ` C )
  assume monsect.1: |- ( ph -> F e. ( X M Y ) )
  assume monsect.2: |- ( ph -> G ( Y S X ) F )


  assert |- ( ph -> F ( X N Y ) G )

  proof
    wph
    cF
    cG
    cX
    cY
    cN
    co
    wbr
    cF
    cG
    cX
    cY
    cS
    co
    wbr
    #
    cG
    cF
    cY
    cX
    cS
    co
    wbr
    #
    wph
    @0
    cG
    cF
    cX
    cY
    cop
    #
    cX
    cC
    cco
    cfv
    #
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
    #
    wph
    cF
    @4
    cX
    cX
    cop
    cY
    @3
    co
    #
    co
    #
    cF
    @6
    @8
    co
    #
    wceq
    @7
    wph
    cF
    cG
    cY
    cX
    cop
    cY
    @3
    co
    co
    #
    cF
    @2
    cY
    @3
    co
    #
    co
    cY
    @5
    cfv
    #
    cF
    @12
    co
    #
    @9
    @10
    wph
    @11
    @13
    cF
    @12
    wph
    cG
    cY
    cX
    cC
    chom
    cfv
    #
    co
    wcel
    #
    cF
    cX
    cY
    @15
    co
    wcel
    #
    @11
    @13
    wceq
    #
    wph
    @1
    @16
    @17
    @18
    w3a
    monsect.2
    wph
    cB
    cC
    cS
    @3
    @5
    cG
    cF
    @15
    cY
    cX
    sectmon.b
    @15
    eqid
    #
    @3
    eqid
    #
    @5
    eqid
    #
    sectmon.s
    sectmon.c
    sectmon.y
    sectmon.x
    issect
    mpbid
    #
    simp3d
    oveq1d
    wph
    cB
    cC
    @3
    cF
    cG
    @15
    cF
    cY
    cX
    cY
    cX
    sectmon.b
    @19
    @20
    sectmon.c
    sectmon.x
    sectmon.y
    sectmon.x
    wph
    @16
    @17
    @18
    @22
    simp2d
    #
    wph
    @16
    @17
    @18
    @22
    simp1d
    #
    sectmon.y
    @23
    catass
    wph
    @14
    cF
    @10
    wph
    cB
    cC
    @3
    @5
    cF
    @15
    cX
    cY
    sectmon.b
    @19
    @21
    sectmon.c
    sectmon.x
    @20
    sectmon.y
    @23
    catlid
    wph
    cB
    cC
    @3
    @5
    cF
    @15
    cX
    cY
    sectmon.b
    @19
    @21
    sectmon.c
    sectmon.x
    @20
    sectmon.y
    @23
    catrid
    eqtr4d
    3eqtr3d
    wph
    cB
    cC
    @3
    cF
    @4
    @15
    @6
    cM
    cX
    cY
    cX
    sectmon.b
    @19
    @20
    sectmon.m
    sectmon.c
    sectmon.x
    sectmon.y
    sectmon.x
    monsect.1
    wph
    cB
    cC
    @3
    cF
    cG
    @15
    cX
    cY
    cX
    sectmon.b
    @19
    @20
    sectmon.c
    sectmon.x
    sectmon.y
    sectmon.x
    @23
    @24
    catcocl
    wph
    cB
    cC
    @5
    @15
    cX
    sectmon.b
    @19
    @21
    sectmon.c
    sectmon.x
    catidcl
    moni
    mpbid
    wph
    cB
    cC
    cS
    @3
    @5
    cF
    cG
    @15
    cX
    cY
    sectmon.b
    @19
    @20
    @21
    sectmon.s
    sectmon.c
    sectmon.x
    sectmon.y
    @23
    @24
    issect2
    mpbird
    monsect.2
    wph
    cB
    cC
    cS
    cF
    cG
    cN
    cX
    cY
    sectmon.b
    monsect.n
    sectmon.c
    sectmon.x
    sectmon.y
    sectmon.s
    isinv
    mpbir2and
end
