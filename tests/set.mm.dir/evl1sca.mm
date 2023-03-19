include "ccrg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1o.mm"
include "cevl.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cmap.mm"
include "cbs.mm"
include "wceq.mm"
include "wf.mm"
include "crg.mm"
include "crngring.mm"
include "adantr.mm"
include "eqid.mm"
include "ply1sclf.mm"
include "syl.mm"
include "ffvelrn.mm"
include "sylancom.mm"
include "cmpl.mm"
include "cps1.mm"
include "ply1bas.mm"
include "evl1val.mm"
include "syldan.mm"
include "cress.mm"
include "cascl.mm"
include "ressid.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "ply1ascl.mm"
include "syl6reqr.mm"
include "fveq1d.mm"
include "con0.mm"
include "evlval.mm"
include "1on.mm"
include "a1i.mm"
include "simpl.mm"
include "csubrg.mm"
include "subrgid.mm"
include "simpr.mm"
include "evlssca.mm"
include "eqtrd.mm"
include "coeq1d.mm"
include "wral.mm"
include "wf1o.mm"
include "c0.mm"
include "df1o2.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "0ex.mm"
include "mapsnf1o3.mm"
include "f1of.mm"
include "mp1i.mm"
include "fmpt.mm"
include "sylibr.mm"
include "eqidd.mm"
include "fconstmpt.mm"
include "fmptcof.mm"
include "syl6eqr.mm"
include "3eqtrd.mm"

theorem evl1sca
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cO: class O
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume evl1sca.o: |- O = ( eval1 ` R )
  assume evl1sca.p: |- P = ( Poly1 ` R )
  assume evl1sca.b: |- B = ( Base ` R )
  assume evl1sca.a: |- A = ( algSc ` P )


  assert |- ( ( R e. CRing /\ X e. B ) -> ( O ` ( A ` X ) ) = ( B X. { X } ) )

  proof
    cR
    ccrg
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cA
    cfv
    #
    cO
    cfv
    #
    @3
    c1o
    cR
    cevl
    co
    #
    cfv
    #
    vy
    cB
    c1o
    vy
    cv
    csn
    cxp
    #
    cmpt
    #
    ccom
    #
    cB
    c1o
    cmap
    co
    #
    cX
    csn
    #
    cxp
    #
    @8
    ccom
    #
    cB
    @11
    cxp
    #
    @0
    @1
    @3
    cP
    cbs
    cfv
    #
    wcel
    #
    @4
    @9
    wceq
    @0
    @1
    cB
    @15
    cA
    wf
    #
    @16
    @2
    cR
    crg
    wcel
    #
    @17
    @0
    @18
    @1
    cR
    crngring
    adantr
    #
    cA
    @15
    cP
    cR
    cB
    evl1sca.p
    evl1sca.a
    evl1sca.b
    @15
    eqid
    #
    ply1sclf
    syl
    cB
    @15
    cX
    cA
    ffvelrn
    sylancom
    vy
    @3
    cB
    @5
    cR
    @15
    c1o
    cR
    cmpl
    co
    #
    cO
    evl1sca.o
    @5
    eqid
    #
    evl1sca.b
    @21
    eqid
    cP
    cR
    cR
    cps1
    cfv
    #
    @15
    evl1sca.p
    @23
    eqid
    @20
    ply1bas
    evl1val
    syldan
    @2
    @6
    @12
    @8
    @2
    @6
    cX
    c1o
    cR
    cB
    cress
    co
    #
    cmpl
    co
    #
    cascl
    cfv
    #
    cfv
    #
    @5
    cfv
    @12
    @2
    @3
    @27
    @5
    @2
    cX
    cA
    @26
    @2
    @26
    @21
    cascl
    cfv
    cA
    @2
    @25
    @21
    cascl
    @2
    @24
    cR
    c1o
    cmpl
    @0
    @24
    cR
    wceq
    @1
    cB
    cR
    ccrg
    evl1sca.b
    ressid
    adantr
    oveq2d
    fveq2d
    cA
    cP
    cR
    evl1sca.p
    evl1sca.a
    ply1ascl
    syl6reqr
    fveq1d
    fveq2d
    @2
    @26
    cB
    @5
    cB
    cR
    @24
    c1o
    con0
    @25
    cX
    cB
    @5
    cR
    c1o
    @22
    evl1sca.b
    evlval
    @25
    eqid
    @24
    eqid
    evl1sca.b
    @26
    eqid
    c1o
    con0
    wcel
    @2
    1on
    a1i
    @0
    @1
    simpl
    @2
    @18
    cB
    cR
    csubrg
    cfv
    wcel
    @19
    cB
    cR
    evl1sca.b
    subrgid
    syl
    @0
    @1
    simpr
    evlssca
    eqtrd
    coeq1d
    @2
    @13
    vy
    cB
    cX
    cmpt
    @14
    @2
    vy
    vx
    cB
    @10
    @7
    cX
    cX
    @8
    @12
    @2
    cB
    @10
    @8
    wf
    #
    @7
    @10
    wcel
    vy
    cB
    wral
    cB
    @10
    @8
    wf1o
    @28
    @2
    vy
    cB
    c1o
    @8
    c0
    df1o2
    cB
    cR
    cbs
    cfv
    cvv
    evl1sca.b
    cR
    cbs
    fvex
    eqeltri
    0ex
    @8
    eqid
    #
    mapsnf1o3
    cB
    @10
    @8
    f1of
    mp1i
    vy
    cB
    @10
    @7
    @8
    @29
    fmpt
    sylibr
    @2
    @8
    eqidd
    @12
    vx
    @10
    cX
    cmpt
    wceq
    @2
    vx
    @10
    cX
    fconstmpt
    a1i
    vx
    cv
    @7
    wceq
    cX
    eqidd
    fmptcof
    vy
    cB
    cX
    fconstmpt
    syl6eqr
    3eqtrd
end
