include "choma.mm"
include "cfv.mm"
include "cxp.mm"
include "cv.mm"
include "csn.mm"
include "cmpt.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "chom.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "fveq1d.mm"
include "xpeq2d.mm"
include "mpteq12dv.mm"
include "df-homa.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem homafval
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cH: class H
  let cJ: class J
  let vc: setvar c
  let vz: setvar z
  let cX: class X
  let cY: class Y
  assume homarcl.h: |- H = ( HomA ` C )
  assume homafval.b: |- B = ( Base ` C )
  assume homafval.c: |- ( ph -> C e. Cat )
  assume homafval.j: |- J = ( Hom ` C )

  disjoint B x
  disjoint C x
  disjoint ph x
  disjoint c x
  disjoint c z
  disjoint B c
  disjoint x z
  disjoint B z
  disjoint C c
  disjoint C z
  disjoint J c
  disjoint J z
  disjoint ph z
  disjoint X z
  disjoint Y z
  assert |- ( ph -> H = ( x e. ( B X. B ) |-> ( { x } X. ( J ` x ) ) ) )

  proof
    wph
    cH
    cC
    choma
    cfv
    #
    vx
    cB
    cB
    cxp
    #
    vx
    cv
    #
    csn
    #
    @2
    cJ
    cfv
    #
    cxp
    #
    cmpt
    #
    homarcl.h
    wph
    cC
    ccat
    wcel
    @0
    @6
    wceq
    homafval.c
    vc
    cC
    vx
    vc
    cv
    #
    cbs
    cfv
    #
    @8
    cxp
    #
    @3
    @2
    @7
    chom
    cfv
    #
    cfv
    #
    cxp
    #
    cmpt
    @6
    ccat
    choma
    @7
    cC
    wceq
    #
    vx
    @9
    @12
    @1
    @5
    @13
    @8
    cB
    @13
    @8
    cC
    cbs
    cfv
    #
    cB
    @7
    cC
    cbs
    fveq2
    homafval.b
    syl6eqr
    sqxpeqd
    @13
    @11
    @4
    @3
    @13
    @2
    @10
    cJ
    @13
    @10
    cC
    chom
    cfv
    cJ
    @7
    cC
    chom
    fveq2
    homafval.j
    syl6eqr
    fveq1d
    xpeq2d
    mpteq12dv
    vx
    vc
    df-homa
    vx
    @1
    @5
    cB
    cB
    cB
    @14
    cvv
    homafval.b
    cC
    cbs
    fvex
    eqeltri
    #
    @15
    xpex
    mptex
    fvmpt
    syl
    syl5eq
end
