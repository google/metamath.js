include "co.mm"
include "wbr.mm"
include "csect.mm"
include "cfv.mm"
include "wa.mm"
include "eqid.mm"
include "isinv.mm"
include "ancom.mm"
include "syl6bb.mm"
include "bitr4d.mm"

theorem invsym
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
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


  assert |- ( ph -> ( F ( X N Y ) G <-> G ( Y N X ) F ) )

  proof
    wph
    cF
    cG
    cX
    cY
    cN
    co
    wbr
    #
    cG
    cF
    cY
    cX
    cC
    csect
    cfv
    #
    co
    wbr
    #
    cF
    cG
    cX
    cY
    @1
    co
    wbr
    #
    wa
    #
    cG
    cF
    cY
    cX
    cN
    co
    wbr
    wph
    @0
    @3
    @2
    wa
    @4
    wph
    cB
    cC
    @1
    cF
    cG
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    @1
    eqid
    #
    isinv
    @3
    @2
    ancom
    syl6bb
    wph
    cB
    cC
    @1
    cG
    cF
    cN
    cY
    cX
    invfval.b
    invfval.n
    invfval.c
    invfval.y
    invfval.x
    @5
    isinv
    bitr4d
end
