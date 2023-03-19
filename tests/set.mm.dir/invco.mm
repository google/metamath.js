include "cop.mm"
include "co.mm"
include "cfv.mm"
include "wbr.mm"
include "csect.mm"
include "eqid.mm"
include "wa.mm"
include "cdm.mm"
include "wcel.mm"
include "isoval.mm"
include "eleqtrd.mm"
include "wfun.mm"
include "wb.mm"
include "invfun.mm"
include "funfvbrb.mm"
include "syl.mm"
include "mpbid.mm"
include "isinv.mm"
include "simpld.mm"
include "sectco.mm"
include "simprd.mm"
include "mpbir2and.mm"

theorem invco
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vz: setvar z
  let cS: class S
  assume invfval.b: |- B = ( Base ` C )
  assume invfval.n: |- N = ( Inv ` C )
  assume invfval.c: |- ( ph -> C e. Cat )
  assume invfval.x: |- ( ph -> X e. B )
  assume invfval.y: |- ( ph -> Y e. B )
  assume isoval.n: |- I = ( Iso ` C )
  assume invinv.f: |- ( ph -> F e. ( X I Y ) )
  assume invco.o: |- .x. = ( comp ` C )
  assume invco.z: |- ( ph -> Z e. B )
  assume invco.f: |- ( ph -> G e. ( Y I Z ) )


  assert |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) ( X N Z ) ( ( ( X N Y ) ` F ) ( <. Z , Y >. .x. X ) ( ( Y N Z ) ` G ) ) )

  proof
    wph
    cG
    cF
    cX
    cY
    cop
    cZ
    c.x
    co
    co
    #
    cF
    cX
    cY
    cN
    co
    #
    cfv
    #
    cG
    cY
    cZ
    cN
    co
    #
    cfv
    #
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
    cN
    co
    wbr
    @0
    @5
    cX
    cZ
    cC
    csect
    cfv
    #
    co
    wbr
    @5
    @0
    cZ
    cX
    @6
    co
    wbr
    wph
    cB
    cC
    @6
    c.x
    cF
    @2
    cG
    @4
    cX
    cY
    cZ
    invfval.b
    invco.o
    @6
    eqid
    #
    invfval.c
    invfval.x
    invfval.y
    invco.z
    wph
    cF
    @2
    cX
    cY
    @6
    co
    wbr
    #
    @2
    cF
    cY
    cX
    @6
    co
    wbr
    #
    wph
    cF
    @2
    @1
    wbr
    #
    @8
    @9
    wa
    wph
    cF
    @1
    cdm
    #
    wcel
    #
    @10
    wph
    cF
    cX
    cY
    cI
    co
    @11
    invinv.f
    wph
    cB
    cC
    cI
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    isoval.n
    isoval
    eleqtrd
    wph
    @1
    wfun
    @12
    @10
    wb
    wph
    cB
    cC
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    invfun
    cF
    @1
    funfvbrb
    syl
    mpbid
    wph
    cB
    cC
    @6
    cF
    @2
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    @7
    isinv
    mpbid
    #
    simpld
    wph
    cG
    @4
    cY
    cZ
    @6
    co
    wbr
    #
    @4
    cG
    cZ
    cY
    @6
    co
    wbr
    #
    wph
    cG
    @4
    @3
    wbr
    #
    @14
    @15
    wa
    wph
    cG
    @3
    cdm
    #
    wcel
    #
    @16
    wph
    cG
    cY
    cZ
    cI
    co
    @17
    invco.f
    wph
    cB
    cC
    cI
    cN
    cY
    cZ
    invfval.b
    invfval.n
    invfval.c
    invfval.y
    invco.z
    isoval.n
    isoval
    eleqtrd
    wph
    @3
    wfun
    @18
    @16
    wb
    wph
    cB
    cC
    cN
    cY
    cZ
    invfval.b
    invfval.n
    invfval.c
    invfval.y
    invco.z
    invfun
    cG
    @3
    funfvbrb
    syl
    mpbid
    wph
    cB
    cC
    @6
    cG
    @4
    cN
    cY
    cZ
    invfval.b
    invfval.n
    invfval.c
    invfval.y
    invco.z
    @7
    isinv
    mpbid
    #
    simpld
    sectco
    wph
    cB
    cC
    @6
    c.x
    @4
    cG
    @2
    cF
    cZ
    cY
    cX
    invfval.b
    invco.o
    @7
    invfval.c
    invco.z
    invfval.y
    invfval.x
    wph
    @14
    @15
    @19
    simprd
    wph
    @8
    @9
    @13
    simprd
    sectco
    wph
    cB
    cC
    @6
    @0
    @5
    cN
    cX
    cZ
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invco.z
    @7
    isinv
    mpbir2and
end
