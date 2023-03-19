include "wcel.mm"
include "csymg.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cts.mm"
include "ctp.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "wf1o.mm"
include "cab.mm"
include "ccom.mm"
include "cmpt2.mm"
include "cpw.mm"
include "csn.mm"
include "cxp.mm"
include "cpt.mm"
include "csb.mm"
include "cmap.mm"
include "co.mm"
include "ovex.mm"
include "wf.mm"
include "f1of.mm"
include "vex.mm"
include "elmap.mm"
include "sylibr.mm"
include "abssi.mm"
include "ssexi.mm"
include "a1i.mm"
include "wa.mm"
include "id.mm"
include "wb.mm"
include "f1oeq23.mm"
include "anidms.mm"
include "abbidv.mm"
include "syl6eqr.mm"
include "sylan9eqr.mm"
include "opeq2d.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "simpl.mm"
include "pweqd.mm"
include "sneqd.mm"
include "xpeq12d.mm"
include "fveq2d.mm"
include "tpeq123d.mm"
include "csbied.mm"
include "df-symg.mm"
include "tpex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem symgval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vf: setvar f
  let vg: setvar g
  let cG: class G
  let cJ: class J
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume symgval.1: |- G = ( SymGrp ` A )
  assume symgval.2: |- B = { x | x : A -1-1-onto-> A }
  assume symgval.3: |- .+ = ( f e. B , g e. B |-> ( f o. g ) )
  assume symgval.4: |- J = ( Xt_ ` ( A X. { ~P A } ) )

  disjoint f g
  disjoint f x
  disjoint A f
  disjoint g x
  disjoint A g
  disjoint A x
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint A a
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint J a
  disjoint J b
  disjoint .+ a
  disjoint .+ b
  assert |- ( A e. V -> G = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. , <. ( TopSet ` ndx ) , J >. } )

  proof
    cA
    cV
    wcel
    #
    cG
    cA
    csymg
    cfv
    #
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    cplusg
    cfv
    #
    c.pl
    cop
    #
    cnx
    cts
    cfv
    #
    cJ
    cop
    #
    ctp
    #
    symgval.1
    @0
    cA
    cvv
    wcel
    @1
    @8
    wceq
    cA
    cV
    elex
    va
    cA
    vb
    va
    cv
    #
    @9
    vx
    cv
    #
    wf1o
    #
    vx
    cab
    #
    @2
    vb
    cv
    #
    cop
    #
    @4
    vf
    vg
    @13
    @13
    vf
    cv
    vg
    cv
    ccom
    #
    cmpt2
    #
    cop
    #
    @6
    @9
    @9
    cpw
    #
    csn
    #
    cxp
    #
    cpt
    cfv
    #
    cop
    #
    ctp
    #
    csb
    @8
    cvv
    csymg
    @9
    cA
    wceq
    #
    vb
    @12
    @23
    @8
    cvv
    @12
    cvv
    wcel
    @24
    @12
    @9
    @9
    cmap
    co
    #
    @9
    @9
    cmap
    ovex
    @11
    vx
    @25
    @11
    @9
    @9
    @10
    wf
    @10
    @25
    wcel
    @9
    @9
    @10
    f1of
    @9
    @9
    @10
    va
    vex
    #
    @26
    elmap
    sylibr
    abssi
    ssexi
    a1i
    @24
    @13
    @12
    wceq
    #
    wa
    #
    @14
    @3
    @17
    @5
    @22
    @7
    @28
    @13
    cB
    @2
    @27
    @24
    @13
    @12
    cB
    @27
    id
    @24
    @12
    cA
    cA
    @10
    wf1o
    #
    vx
    cab
    cB
    @24
    @11
    @29
    vx
    @24
    @11
    @29
    wb
    @9
    cA
    @9
    cA
    @10
    f1oeq23
    anidms
    abbidv
    symgval.2
    syl6eqr
    sylan9eqr
    #
    opeq2d
    @28
    @16
    c.pl
    @4
    @28
    @16
    vf
    vg
    cB
    cB
    @15
    cmpt2
    c.pl
    @28
    vf
    vg
    @13
    @13
    @15
    cB
    cB
    @15
    @30
    @30
    @28
    @15
    eqidd
    mpt2eq123dv
    symgval.3
    syl6eqr
    opeq2d
    @28
    @21
    cJ
    @6
    @28
    @21
    cA
    cA
    cpw
    #
    csn
    #
    cxp
    #
    cpt
    cfv
    cJ
    @28
    @20
    @33
    cpt
    @28
    @9
    cA
    @19
    @32
    @24
    @27
    simpl
    #
    @28
    @18
    @31
    @28
    @9
    cA
    @34
    pweqd
    sneqd
    xpeq12d
    fveq2d
    symgval.4
    syl6eqr
    opeq2d
    tpeq123d
    csbied
    va
    vf
    vg
    vx
    vb
    df-symg
    @3
    @5
    @7
    tpex
    fvmpt
    syl
    syl5eq
end
