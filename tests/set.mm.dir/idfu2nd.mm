include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "cop.mm"
include "cid.mm"
include "cres.mm"
include "df-ov.mm"
include "cv.mm"
include "cxp.mm"
include "cvv.mm"
include "cmpt.mm"
include "idfuval.mm"
include "fveq2d.mm"
include "wcel.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "xpex.mm"
include "mptex.mm"
include "op2nd.mm"
include "syl6eq.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "syl6eqr.mm"
include "reseq2d.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "ovex.mm"
include "mp1i.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem idfu2nd
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cH: class H
  let cI: class I
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vc: setvar c
  let vz: setvar z
  assume idfuval.i: |- I = ( idFunc ` C )
  assume idfuval.b: |- B = ( Base ` C )
  assume idfuval.c: |- ( ph -> C e. Cat )
  assume idfuval.h: |- H = ( Hom ` C )
  assume idfu2nd.x: |- ( ph -> X e. B )
  assume idfu2nd.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X ( 2nd ` I ) Y ) = ( _I |` ( X H Y ) ) )

  proof
    wph
    cX
    cY
    cI
    c2nd
    cfv
    #
    co
    cX
    cY
    cop
    #
    @0
    cfv
    cid
    cX
    cY
    cH
    co
    #
    cres
    #
    cX
    cY
    @0
    df-ov
    wph
    vz
    @1
    cid
    vz
    cv
    #
    cH
    cfv
    #
    cres
    #
    @3
    cB
    cB
    cxp
    #
    @0
    cvv
    wph
    @0
    cid
    cB
    cres
    #
    vz
    @7
    @6
    cmpt
    #
    cop
    #
    c2nd
    cfv
    @9
    wph
    cI
    @10
    c2nd
    wph
    vz
    cB
    cC
    cH
    cI
    idfuval.i
    idfuval.b
    idfuval.c
    idfuval.h
    idfuval
    fveq2d
    @8
    @9
    cB
    cvv
    wcel
    @8
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
    @7
    @6
    cB
    cB
    @11
    @11
    xpex
    mptex
    op2nd
    syl6eq
    wph
    @4
    @1
    wceq
    #
    wa
    #
    @5
    @2
    cid
    @13
    @5
    @1
    cH
    cfv
    @2
    @13
    @4
    @1
    cH
    wph
    @12
    simpr
    fveq2d
    cX
    cY
    cH
    df-ov
    syl6eqr
    reseq2d
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    @1
    @7
    wcel
    idfu2nd.x
    idfu2nd.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    wph
    cX
    cY
    cH
    ovex
    @2
    cvv
    resiexg
    mp1i
    fvmptd
    syl5eq
end
