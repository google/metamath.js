include "c1st.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "cxp.mm"
include "cv.mm"
include "chom.mm"
include "cmpt.mm"
include "cop.mm"
include "eqid.mm"
include "idfuval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "xpex.mm"
include "mptex.mm"
include "op1st.mm"
include "syl6eq.mm"

theorem idfu1st
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cI: class I
  let vb: setvar b
  let vc: setvar c
  let vz: setvar z
  let cH: class H
  let cX: class X
  let cY: class Y
  assume idfuval.i: |- I = ( idFunc ` C )
  assume idfuval.b: |- B = ( Base ` C )
  assume idfuval.c: |- ( ph -> C e. Cat )


  assert |- ( ph -> ( 1st ` I ) = ( _I |` B ) )

  proof
    wph
    cI
    c1st
    cfv
    cid
    cB
    cres
    #
    vz
    cB
    cB
    cxp
    #
    cid
    vz
    cv
    cC
    chom
    cfv
    #
    cfv
    cres
    #
    cmpt
    #
    cop
    #
    c1st
    cfv
    @0
    wph
    cI
    @5
    c1st
    wph
    vz
    cB
    cC
    @2
    cI
    idfuval.i
    idfuval.b
    idfuval.c
    @2
    eqid
    idfuval
    fveq2d
    @0
    @4
    cB
    cvv
    wcel
    @0
    cvv
    wcel
    cB
    cC
    cbs
    cfv
    cvv
    idfuval.b
    cC
    cbs
    fvex
    eqeltri
    #
    cB
    cvv
    resiexg
    ax-mp
    vz
    @1
    @3
    cB
    cB
    @6
    @6
    xpex
    mptex
    op1st
    syl6eq
end
