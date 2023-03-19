include "cidfu.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "cxp.mm"
include "cv.mm"
include "cmpt.mm"
include "cop.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "chom.mm"
include "csb.mm"
include "cvv.mm"
include "fvexd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "wa.mm"
include "simpr.mm"
include "reseq2d.mm"
include "sqxpeqd.mm"
include "simpl.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "mpteq12dv.mm"
include "opeq12d.mm"
include "csbied2.mm"
include "df-idfu.mm"
include "opex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem idfuval
  let wph: wff ph
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cH: class H
  let cI: class I
  let vb: setvar b
  let vc: setvar c
  let cX: class X
  let cY: class Y
  assume idfuval.i: |- I = ( idFunc ` C )
  assume idfuval.b: |- B = ( Base ` C )
  assume idfuval.c: |- ( ph -> C e. Cat )
  assume idfuval.h: |- H = ( Hom ` C )

  disjoint B z
  disjoint C z
  disjoint H z
  disjoint ph z
  disjoint b c
  disjoint b z
  disjoint B b
  disjoint c z
  disjoint B c
  disjoint C b
  disjoint C c
  disjoint H b
  disjoint H c
  disjoint X z
  disjoint Y z
  assert |- ( ph -> I = <. ( _I |` B ) , ( z e. ( B X. B ) |-> ( _I |` ( H ` z ) ) ) >. )

  proof
    wph
    cI
    cC
    cidfu
    cfv
    #
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
    #
    cH
    cfv
    #
    cres
    #
    cmpt
    #
    cop
    #
    idfuval.i
    wph
    cC
    ccat
    wcel
    @0
    @7
    wceq
    idfuval.c
    vc
    cC
    vb
    vc
    cv
    #
    cbs
    cfv
    #
    cid
    vb
    cv
    #
    cres
    #
    vz
    @10
    @10
    cxp
    #
    cid
    @3
    @8
    chom
    cfv
    #
    cfv
    #
    cres
    #
    cmpt
    #
    cop
    #
    csb
    @7
    ccat
    cidfu
    @8
    cC
    wceq
    #
    vb
    @9
    cB
    @17
    @7
    cvv
    @18
    @8
    cbs
    fvexd
    @18
    @9
    cC
    cbs
    cfv
    cB
    @8
    cC
    cbs
    fveq2
    idfuval.b
    syl6eqr
    @18
    @10
    cB
    wceq
    #
    wa
    #
    @11
    @1
    @16
    @6
    @20
    @10
    cB
    cid
    @18
    @19
    simpr
    #
    reseq2d
    @20
    vz
    @12
    @15
    @2
    @5
    @20
    @10
    cB
    @21
    sqxpeqd
    @20
    @14
    @4
    cid
    @20
    @3
    @13
    cH
    @20
    @13
    cC
    chom
    cfv
    cH
    @20
    @8
    cC
    chom
    @18
    @19
    simpl
    fveq2d
    idfuval.h
    syl6eqr
    fveq1d
    reseq2d
    mpteq12dv
    opeq12d
    csbied2
    vz
    vc
    vb
    df-idfu
    @1
    @6
    opex
    fvmpt
    syl
    syl5eq
end
