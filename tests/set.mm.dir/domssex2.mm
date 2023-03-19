include "wf1.mm"
include "wcel.mm"
include "w3a.mm"
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
include "cvv.mm"
include "ccom.mm"
include "cid.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "wf.mm"
include "f1f.mm"
include "fex2.mm"
include "syl3an1.mm"
include "f1stres.mm"
include "a1i.mm"
include "difexg.mm"
include "3ad2ant3.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "syl3anc.mm"
include "unexg.mm"
include "syl2anc.mm"
include "cnvexg.mm"
include "syl.mm"
include "wss.mm"
include "wf1o.mm"
include "eqid.mm"
include "domss2.mm"
include "simp1d.mm"
include "f1of1.mm"
include "ssv.mm"
include "f1ss.mm"
include "simp3d.mm"
include "jca.mm"
include "f1eq1.mm"
include "coeq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"

theorem domssex2
  let cA: class A
  let cB: class B
  let vg: setvar g
  let cF: class F
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vx: setvar x

  disjoint A g
  disjoint B g
  disjoint F g
  disjoint f g
  disjoint f x
  disjoint A f
  disjoint g x
  disjoint A x
  disjoint B f
  disjoint B x
  disjoint W f
  assert |- ( ( F : A -1-1-> B /\ A e. V /\ B e. W ) -> E. g ( g : B -1-1-> _V /\ ( g o. F ) = ( _I |` A ) ) )

  proof
    cA
    cB
    cF
    wf1
    #
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    w3a
    #
    cF
    c1st
    cB
    cF
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
    cvv
    wcel
    #
    cB
    cvv
    @11
    wf1
    #
    @11
    cF
    ccom
    #
    cid
    cA
    cres
    #
    wceq
    #
    wa
    #
    cB
    cvv
    vg
    cv
    #
    wf1
    #
    @18
    cF
    ccom
    #
    @15
    wceq
    #
    wa
    #
    vg
    wex
    @3
    @10
    cvv
    wcel
    #
    @12
    @3
    cF
    cvv
    wcel
    #
    @9
    cvv
    wcel
    #
    @23
    @0
    cA
    cB
    cF
    wf
    @1
    @2
    @24
    cA
    cB
    cF
    f1f
    cA
    cB
    cF
    cV
    cW
    fex2
    syl3an1
    @3
    @8
    @5
    @9
    wf
    #
    @8
    cvv
    wcel
    #
    @5
    cvv
    wcel
    #
    @25
    @26
    @3
    @5
    @7
    f1stres
    a1i
    @3
    @28
    @7
    cvv
    wcel
    @27
    @2
    @0
    @28
    @1
    cB
    @4
    cW
    difexg
    3ad2ant3
    #
    @6
    snex
    @5
    @7
    cvv
    cvv
    xpexg
    sylancl
    @29
    @8
    @5
    @9
    cvv
    cvv
    fex2
    syl3anc
    cF
    @9
    cvv
    cvv
    unexg
    syl2anc
    @10
    cvv
    cnvexg
    syl
    @3
    @13
    @16
    @3
    cB
    @11
    crn
    #
    @11
    wf1
    #
    @30
    cvv
    wss
    @13
    @3
    cB
    @30
    @11
    wf1o
    #
    @31
    @3
    @32
    cA
    @30
    wss
    #
    @16
    cA
    cB
    cF
    @11
    cV
    cW
    @11
    eqid
    domss2
    #
    simp1d
    cB
    @30
    @11
    f1of1
    syl
    @30
    ssv
    cB
    @30
    cvv
    @11
    f1ss
    sylancl
    @3
    @32
    @33
    @16
    @34
    simp3d
    jca
    @22
    @17
    vg
    @11
    cvv
    @18
    @11
    wceq
    #
    @19
    @13
    @21
    @16
    cB
    cvv
    @18
    @11
    f1eq1
    @35
    @20
    @14
    @15
    @18
    @11
    cF
    coeq1
    eqeq1d
    anbi12d
    spcegv
    sylc
end
