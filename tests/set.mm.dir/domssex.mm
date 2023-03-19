include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "cvv.mm"
include "wcel.mm"
include "wss.mm"
include "cen.mm"
include "wa.mm"
include "brdomi.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "wi.mm"
include "c1st.mm"
include "crn.mm"
include "cdif.mm"
include "cuni.mm"
include "cpw.mm"
include "csn.mm"
include "cxp.mm"
include "cres.mm"
include "cun.mm"
include "ccnv.mm"
include "vex.mm"
include "wf.mm"
include "f1stres.mm"
include "a1i.mm"
include "difexg.mm"
include "adantl.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "fex2.mm"
include "syl3anc.mm"
include "unexg.mm"
include "sylancr.mm"
include "cnvexg.mm"
include "syl.mm"
include "rnexg.mm"
include "wf1o.mm"
include "ccom.mm"
include "cid.mm"
include "wceq.mm"
include "w3a.mm"
include "simpl.mm"
include "cdm.mm"
include "f1dm.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "adantr.mm"
include "simpr.mm"
include "eqid.mm"
include "domss2.mm"
include "simp2d.mm"
include "simp1d.mm"
include "f1oen3g.mm"
include "syl2anc.mm"
include "jca.mm"
include "sseq2.mm"
include "breq2.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "ex.mm"
include "exlimiv.mm"

theorem domssex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cW: class W

  disjoint A x
  disjoint B x
  disjoint f g
  disjoint f x
  disjoint A f
  disjoint g x
  disjoint A g
  disjoint B f
  disjoint B g
  disjoint F g
  disjoint W f
  assert |- ( A ~<_ B -> E. x ( A C_ x /\ B ~~ x ) )

  proof
    cA
    cB
    cdom
    wbr
    cA
    cB
    vf
    cv
    #
    wf1
    #
    vf
    wex
    cB
    cvv
    wcel
    #
    cA
    vx
    cv
    #
    wss
    #
    cB
    @3
    cen
    wbr
    #
    wa
    #
    vx
    wex
    #
    cA
    cB
    vf
    brdomi
    cA
    cB
    cdom
    reldom
    brrelex2i
    @1
    @2
    @7
    wi
    vf
    @1
    @2
    @7
    @1
    @2
    wa
    #
    @0
    c1st
    cB
    @0
    crn
    #
    cdif
    #
    cA
    crn
    cuni
    cpw
    #
    csn
    #
    cxp
    #
    cres
    #
    cun
    #
    ccnv
    #
    crn
    #
    cvv
    wcel
    #
    cA
    @17
    wss
    #
    cB
    @17
    cen
    wbr
    #
    wa
    #
    @7
    @8
    @16
    cvv
    wcel
    #
    @18
    @8
    @15
    cvv
    wcel
    #
    @22
    @8
    @0
    cvv
    wcel
    @14
    cvv
    wcel
    #
    @23
    vf
    vex
    #
    @8
    @13
    @10
    @14
    wf
    #
    @13
    cvv
    wcel
    #
    @10
    cvv
    wcel
    #
    @24
    @26
    @8
    @10
    @12
    f1stres
    a1i
    @8
    @28
    @12
    cvv
    wcel
    @27
    @2
    @28
    @1
    cB
    @9
    cvv
    difexg
    adantl
    #
    @11
    snex
    @10
    @12
    cvv
    cvv
    xpexg
    sylancl
    @29
    @13
    @10
    @14
    cvv
    cvv
    fex2
    syl3anc
    @0
    @14
    cvv
    cvv
    unexg
    sylancr
    @15
    cvv
    cnvexg
    syl
    #
    @16
    cvv
    rnexg
    syl
    @8
    @19
    @20
    @8
    cB
    @17
    @16
    wf1o
    #
    @19
    @16
    @0
    ccom
    cid
    cA
    cres
    wceq
    #
    @8
    @1
    cA
    cvv
    wcel
    #
    @2
    @31
    @19
    @32
    w3a
    @1
    @2
    simpl
    @1
    @33
    @2
    @1
    cA
    @0
    cdm
    cvv
    cA
    cB
    @0
    f1dm
    @0
    @25
    dmex
    syl6eqelr
    adantr
    @1
    @2
    simpr
    cA
    cB
    @0
    @16
    cvv
    cvv
    @16
    eqid
    domss2
    syl3anc
    #
    simp2d
    @8
    @22
    @31
    @20
    @30
    @8
    @31
    @19
    @32
    @34
    simp1d
    cB
    @17
    @16
    cvv
    f1oen3g
    syl2anc
    jca
    @6
    @21
    vx
    @17
    cvv
    @3
    @17
    wceq
    @4
    @19
    @5
    @20
    @3
    @17
    cA
    sseq2
    @3
    @17
    cB
    cen
    breq2
    anbi12d
    spcegv
    sylc
    ex
    exlimiv
    sylc
end
