include "c1stf.mm"
include "co.mm"
include "c1st.mm"
include "cres.mm"
include "cv.mm"
include "cmpt2.mm"
include "cop.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cxpc.mm"
include "chom.mm"
include "csb.mm"
include "wa.mm"
include "cvv.mm"
include "fvex.mm"
include "xpex.mm"
include "a1i.mm"
include "simpl.mm"
include "fveq2d.mm"
include "simpr.mm"
include "xpeq12d.mm"
include "eqid.mm"
include "xpcbas.mm"
include "eqtr4i.mm"
include "syl6eq.mm"
include "reseq2d.mm"
include "simpll.mm"
include "simplr.mm"
include "oveq12d.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "mpt2eq123dv.mm"
include "opeq12d.mm"
include "csbied2.mm"
include "df-1stf.mm"
include "opex.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"
include "syl5eq.mm"

theorem 1stfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cT: class T
  let cH: class H
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cR: class R
  let cS: class S
  assume 1stfval.t: |- T = ( C Xc. D )
  assume 1stfval.b: |- B = ( Base ` T )
  assume 1stfval.h: |- H = ( Hom ` T )
  assume 1stfval.c: |- ( ph -> C e. Cat )
  assume 1stfval.d: |- ( ph -> D e. Cat )
  assume 1stfval.p: |- P = ( C 1stF D )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint H x
  disjoint H y
  disjoint ph x
  disjoint ph y
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint c d
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint d x
  disjoint d y
  disjoint B d
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  assert |- ( ph -> P = <. ( 1st |` B ) , ( x e. B , y e. B |-> ( 1st |` ( x H y ) ) ) >. )

  proof
    wph
    cP
    cC
    cD
    c1stf
    co
    #
    c1st
    cB
    cres
    #
    vx
    vy
    cB
    cB
    c1st
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    cres
    #
    cmpt2
    #
    cop
    #
    1stfval.p
    wph
    cC
    ccat
    wcel
    cD
    ccat
    wcel
    @0
    @7
    wceq
    1stfval.c
    1stfval.d
    vc
    vd
    cC
    cD
    ccat
    ccat
    vb
    vc
    cv
    #
    cbs
    cfv
    #
    vd
    cv
    #
    cbs
    cfv
    #
    cxp
    #
    c1st
    vb
    cv
    #
    cres
    #
    vx
    vy
    @13
    @13
    c1st
    @2
    @3
    @8
    @10
    cxpc
    co
    #
    chom
    cfv
    #
    co
    #
    cres
    #
    cmpt2
    #
    cop
    #
    csb
    @7
    c1stf
    @8
    cC
    wceq
    #
    @10
    cD
    wceq
    #
    wa
    #
    vb
    @12
    cB
    @20
    @7
    cvv
    @12
    cvv
    wcel
    @23
    @9
    @11
    @8
    cbs
    fvex
    @10
    cbs
    fvex
    xpex
    a1i
    @23
    @12
    cC
    cbs
    cfv
    #
    cD
    cbs
    cfv
    #
    cxp
    #
    cB
    @23
    @9
    @24
    @11
    @25
    @23
    @8
    cC
    cbs
    @21
    @22
    simpl
    fveq2d
    @23
    @10
    cD
    cbs
    @21
    @22
    simpr
    fveq2d
    xpeq12d
    @26
    cT
    cbs
    cfv
    cB
    cC
    cD
    cT
    @24
    @25
    1stfval.t
    @24
    eqid
    @25
    eqid
    xpcbas
    1stfval.b
    eqtr4i
    syl6eq
    @23
    @13
    cB
    wceq
    #
    wa
    #
    @14
    @1
    @19
    @6
    @28
    @13
    cB
    c1st
    @23
    @27
    simpr
    #
    reseq2d
    @28
    vx
    vy
    @13
    @13
    @18
    cB
    cB
    @5
    @29
    @29
    @28
    @17
    @4
    c1st
    @28
    @16
    cH
    @2
    @3
    @28
    @16
    cT
    chom
    cfv
    cH
    @28
    @15
    cT
    chom
    @28
    @15
    cC
    cD
    cxpc
    co
    cT
    @28
    @8
    cC
    @10
    cD
    cxpc
    @21
    @22
    @27
    simpll
    @21
    @22
    @27
    simplr
    oveq12d
    1stfval.t
    syl6eqr
    fveq2d
    1stfval.h
    syl6eqr
    oveqd
    reseq2d
    mpt2eq123dv
    opeq12d
    csbied2
    vx
    vy
    vd
    vc
    vb
    df-1stf
    @1
    @6
    opex
    ovmpt2a
    syl2anc
    syl5eq
end
