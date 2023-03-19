include "cv.mm"
include "co.mm"
include "ccnv.mm"
include "cin.mm"
include "cvv.mm"
include "invffval.mm"
include "wceq.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "cnveqd.mm"
include "ineq12d.mm"
include "wcel.mm"
include "ovex.mm"
include "inex1.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem invfval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
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
  assume invfval.b: |- B = ( Base ` C )
  assume invfval.n: |- N = ( Inv ` C )
  assume invfval.c: |- ( ph -> C e. Cat )
  assume invfval.x: |- ( ph -> X e. B )
  assume invfval.y: |- ( ph -> Y e. B )
  assume invfval.s: |- S = ( Sect ` C )


  assert |- ( ph -> ( X N Y ) = ( ( X S Y ) i^i `' ( Y S X ) ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    cS
    co
    #
    @1
    @0
    cS
    co
    #
    ccnv
    #
    cin
    cX
    cY
    cS
    co
    #
    cY
    cX
    cS
    co
    #
    ccnv
    #
    cin
    #
    cN
    cvv
    wph
    vx
    vy
    cB
    cC
    cS
    cN
    cX
    cX
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.x
    invfval.s
    invffval
    wph
    @0
    cX
    wceq
    #
    @1
    cY
    wceq
    #
    wa
    wa
    #
    @2
    @5
    @4
    @7
    @11
    @0
    cX
    @1
    cY
    cS
    wph
    @9
    @10
    simprl
    #
    wph
    @9
    @10
    simprr
    #
    oveq12d
    @11
    @3
    @6
    @11
    @1
    cY
    @0
    cX
    cS
    @13
    @12
    oveq12d
    cnveqd
    ineq12d
    invfval.x
    invfval.y
    @8
    cvv
    wcel
    wph
    @5
    @7
    cX
    cY
    cS
    ovex
    inex1
    a1i
    ovmpt2d
end
