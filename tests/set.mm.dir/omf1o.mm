include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "comu.mm"
include "co.mm"
include "wf1o.mm"
include "ccnv.mm"
include "ccom.mm"
include "cv.mm"
include "coa.mm"
include "cmpt2.mm"
include "csn.mm"
include "cuni.mm"
include "cmpt.mm"
include "eqid.mm"
include "omxpenlem.mm"
include "ancoms.mm"
include "xpcomf1o.mm"
include "f1oco.mm"
include "sylancl.mm"
include "wceq.mm"
include "wb.mm"
include "xpcomco.mm"
include "eqtr4i.mm"
include "f1oeq1.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "f1ocnv.mm"
include "syl.mm"
include "syl2anc.mm"

theorem omf1o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vz: setvar z
  assume omf1o.1: |- F = ( x e. B , y e. A |-> ( ( A .o x ) +o y ) )
  assume omf1o.2: |- G = ( x e. B , y e. A |-> ( ( B .o y ) +o x ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  assert |- ( ( A e. On /\ B e. On ) -> ( G o. `' F ) : ( A .o B ) -1-1-onto-> ( B .o A ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cB
    cA
    cxp
    #
    cB
    cA
    comu
    co
    #
    cG
    wf1o
    #
    cA
    cB
    comu
    co
    #
    @3
    cF
    ccnv
    #
    wf1o
    #
    @6
    @4
    cG
    @7
    ccom
    wf1o
    @2
    @3
    @4
    vy
    vx
    cA
    cB
    cB
    vy
    cv
    comu
    co
    vx
    cv
    coa
    co
    #
    cmpt2
    #
    vz
    @3
    vz
    cv
    csn
    ccnv
    cuni
    cmpt
    #
    ccom
    #
    wf1o
    #
    @5
    @2
    cA
    cB
    cxp
    #
    @4
    @10
    wf1o
    #
    @3
    @14
    @11
    wf1o
    @13
    @1
    @0
    @15
    vy
    vx
    cB
    cA
    @10
    @10
    eqid
    #
    omxpenlem
    ancoms
    vz
    cB
    cA
    @11
    @11
    eqid
    #
    xpcomf1o
    @3
    @14
    @4
    @10
    @11
    f1oco
    sylancl
    cG
    @12
    wceq
    @5
    @13
    wb
    cG
    vx
    vy
    cB
    cA
    @9
    cmpt2
    @12
    omf1o.2
    vz
    vy
    vx
    cB
    cA
    @9
    @11
    @10
    @17
    @16
    xpcomco
    eqtr4i
    @3
    @4
    cG
    @12
    f1oeq1
    ax-mp
    sylibr
    @2
    @3
    @6
    cF
    wf1o
    @8
    vx
    vy
    cA
    cB
    cF
    omf1o.1
    omxpenlem
    @3
    @6
    cF
    f1ocnv
    syl
    @6
    @3
    @4
    cG
    @7
    f1oco
    syl2anc
end
