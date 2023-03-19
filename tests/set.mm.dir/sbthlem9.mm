include "cv.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "crn.mm"
include "wss.mm"
include "ccnv.mm"
include "wf1.mm"
include "wf1o.mm"
include "sbthlem7.mm"
include "sbthlem5.mm"
include "adantrl.mm"
include "anim12i.mm"
include "an42s.mm"
include "adantlr.mm"
include "sbthlem8.mm"
include "adantll.mm"
include "simpr.mm"
include "anim1i.mm"
include "df-rn.mm"
include "sbthlem6.mm"
include "syl5eqr.mm"
include "sylanr1.mm"
include "jca32.mm"
include "wf.mm"
include "df-f1.mm"
include "wfn.mm"
include "df-f.mm"
include "df-fn.mm"
include "anbi1i.mm"
include "bitri.mm"
include "anbi12i.mm"
include "dff1o4.mm"
include "3imtr4i.mm"

theorem sbthlem9
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  assume sbthlem.1: |- A e. _V
  assume sbthlem.2: |- D = { x | ( x C_ A /\ ( g " ( B \ ( f " x ) ) ) C_ ( A \ x ) ) }
  assume sbthlem.3: |- H = ( ( f |` U. D ) u. ( `' g |` ( A \ U. D ) ) )

  disjoint H x
  disjoint A x
  disjoint B x
  disjoint D x
  disjoint f x
  disjoint g x
  assert |- ( ( f : A -1-1-> B /\ g : B -1-1-> A ) -> H : A -1-1-onto-> B )

  proof
    vf
    cv
    #
    wfun
    #
    @0
    cdm
    cA
    wceq
    #
    wa
    #
    @0
    crn
    cB
    wss
    #
    wa
    #
    @0
    ccnv
    wfun
    #
    wa
    #
    vg
    cv
    #
    wfun
    #
    @8
    cdm
    cB
    wceq
    #
    wa
    #
    @8
    crn
    cA
    wss
    #
    wa
    #
    @8
    ccnv
    wfun
    #
    wa
    #
    wa
    #
    cH
    wfun
    #
    cH
    cdm
    cA
    wceq
    #
    wa
    #
    cH
    ccnv
    #
    wfun
    #
    @20
    cdm
    #
    cB
    wceq
    #
    wa
    #
    wa
    #
    cA
    cB
    @0
    wf1
    #
    cB
    cA
    @8
    wf1
    #
    wa
    cA
    cB
    cH
    wf1o
    #
    @16
    @19
    @21
    @23
    @5
    @15
    @19
    @6
    @3
    @15
    @19
    @4
    @1
    @14
    @2
    @13
    @19
    @1
    @14
    wa
    @17
    @2
    @13
    wa
    @18
    vx
    cA
    cB
    cD
    vf
    vg
    cH
    sbthlem.1
    sbthlem.2
    sbthlem.3
    sbthlem7
    @2
    @12
    @18
    @11
    vx
    cA
    cB
    cD
    vf
    vg
    cH
    sbthlem.1
    sbthlem.2
    sbthlem.3
    sbthlem5
    adantrl
    anim12i
    an42s
    adantlr
    adantlr
    @6
    @15
    @21
    @5
    vx
    cA
    cB
    cD
    vf
    vg
    cH
    sbthlem.1
    sbthlem.2
    sbthlem.3
    sbthlem8
    adantll
    @5
    @15
    @23
    @6
    @4
    @15
    @23
    @3
    @13
    @4
    @10
    @12
    wa
    #
    @14
    @23
    @11
    @10
    @12
    @9
    @10
    simpr
    anim1i
    @4
    @29
    @14
    wa
    wa
    @22
    cH
    crn
    cB
    cH
    df-rn
    vx
    cA
    cB
    cD
    vf
    vg
    cH
    sbthlem.1
    sbthlem.2
    sbthlem.3
    sbthlem6
    syl5eqr
    sylanr1
    adantll
    adantlr
    jca32
    @26
    @7
    @27
    @15
    @26
    cA
    cB
    @0
    wf
    #
    @6
    wa
    @7
    cA
    cB
    @0
    df-f1
    @30
    @5
    @6
    @30
    @0
    cA
    wfn
    #
    @4
    wa
    @5
    cA
    cB
    @0
    df-f
    @31
    @3
    @4
    @0
    cA
    df-fn
    anbi1i
    bitri
    anbi1i
    bitri
    @27
    cB
    cA
    @8
    wf
    #
    @14
    wa
    @15
    cB
    cA
    @8
    df-f1
    @32
    @13
    @14
    @32
    @8
    cB
    wfn
    #
    @12
    wa
    @13
    cB
    cA
    @8
    df-f
    @33
    @11
    @12
    @8
    cB
    df-fn
    anbi1i
    bitri
    anbi1i
    bitri
    anbi12i
    @28
    cH
    cA
    wfn
    #
    @20
    cB
    wfn
    #
    wa
    @25
    cA
    cB
    cH
    dff1o4
    @34
    @19
    @35
    @24
    cH
    cA
    df-fn
    @20
    cB
    df-fn
    anbi12i
    bitri
    3imtr4i
end
