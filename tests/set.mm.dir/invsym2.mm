include "co.mm"
include "ccnv.mm"
include "wrel.mm"
include "wa.mm"
include "wceq.mm"
include "chom.mm"
include "cfv.mm"
include "cxp.mm"
include "wss.mm"
include "eqid.mm"
include "invss.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "relcnv.mm"
include "jctil.mm"
include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "invsym.mm"
include "vex.mm"
include "brcnv.mm"
include "df-br.mm"
include "bitr3i.mm"
include "3bitr3g.mm"
include "eqrelrdv2.mm"
include "mpancom.mm"

theorem invsym2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cN: class N
  let cX: class X
  let cY: class Y
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


  assert |- ( ph -> `' ( X N Y ) = ( Y N X ) )

  proof
    cX
    cY
    cN
    co
    #
    ccnv
    #
    wrel
    #
    cY
    cX
    cN
    co
    #
    wrel
    #
    wa
    wph
    @1
    @3
    wceq
    wph
    @4
    @2
    wph
    @3
    cY
    cX
    cC
    chom
    cfv
    #
    co
    #
    cX
    cY
    @5
    co
    #
    cxp
    #
    wss
    @8
    wrel
    @4
    wph
    cB
    cC
    @5
    cN
    cY
    cX
    invfval.b
    invfval.n
    invfval.c
    invfval.y
    invfval.x
    @5
    eqid
    invss
    @6
    @7
    relxp
    @3
    @8
    relss
    mpisyl
    @0
    relcnv
    jctil
    wph
    vg
    vf
    @1
    @3
    wph
    vf
    cv
    #
    vg
    cv
    #
    @0
    wbr
    #
    @10
    @9
    @3
    wbr
    @10
    @9
    cop
    #
    @1
    wcel
    #
    @12
    @3
    wcel
    wph
    cB
    cC
    @9
    @10
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    invsym
    @11
    @10
    @9
    @1
    wbr
    @13
    @10
    @9
    @0
    vg
    vex
    vf
    vex
    brcnv
    @10
    @9
    @1
    df-br
    bitr3i
    @10
    @9
    @3
    df-br
    3bitr3g
    eqrelrdv2
    mpancom
end
