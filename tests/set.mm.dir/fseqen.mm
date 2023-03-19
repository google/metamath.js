include "cxp.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wcel.mm"
include "com.mm"
include "cmap.mm"
include "co.mm"
include "ciun.mm"
include "c0.mm"
include "wne.mm"
include "bren.mm"
include "n0.mm"
include "wa.mm"
include "eeanv.mm"
include "cdom.mm"
include "cvv.mm"
include "cdm.mm"
include "csuc.mm"
include "cres.mm"
include "cfv.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cop.mm"
include "csn.mm"
include "cseqom.mm"
include "wf1.mm"
include "omex.mm"
include "crn.mm"
include "wfo.mm"
include "wceq.mm"
include "simpl.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "vex.mm"
include "rnex.mm"
include "syl6eqelr.mm"
include "xpexg.mm"
include "sylancr.mm"
include "simpr.mm"
include "eqid.mm"
include "fseqenlem2.mm"
include "f1domg.mm"
include "sylc.mm"
include "fseqdom.mm"
include "syl.mm"
include "sbth.mm"
include "syl2anc.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem fseqen
  let cA: class A
  let vn: setvar n
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y

  disjoint A n
  disjoint b f
  disjoint b g
  disjoint b k
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint f g
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g k
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( ( ( A X. A ) ~~ A /\ A =/= (/) ) -> U_ n e. _om ( A ^m n ) ~~ ( _om X. A ) )

  proof
    cA
    cA
    cxp
    #
    cA
    cen
    wbr
    @0
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    vb
    cv
    #
    cA
    wcel
    #
    vb
    wex
    #
    vn
    com
    cA
    vn
    cv
    cmap
    co
    ciun
    #
    com
    cA
    cxp
    #
    cen
    wbr
    #
    cA
    c0
    wne
    @0
    cA
    vf
    bren
    vb
    cA
    n0
    @3
    @6
    wa
    @2
    @5
    wa
    #
    vb
    wex
    vf
    wex
    @9
    @2
    @5
    vf
    vb
    eeanv
    @10
    @9
    vf
    vb
    @10
    @7
    @8
    cdom
    wbr
    #
    @8
    @7
    cdom
    wbr
    #
    @9
    @10
    @8
    cvv
    wcel
    #
    @7
    @8
    vx
    @7
    vx
    cv
    #
    cdm
    #
    @14
    @15
    vk
    vg
    cvv
    cvv
    vy
    cA
    vk
    cv
    #
    csuc
    cmap
    co
    vy
    cv
    #
    @16
    cres
    vg
    cv
    cfv
    @16
    @17
    cfv
    @1
    co
    cmpt
    cmpt2
    c0
    @4
    cop
    csn
    cseqom
    #
    cfv
    cfv
    cop
    cmpt
    #
    wf1
    @11
    @10
    com
    cvv
    wcel
    cA
    cvv
    wcel
    #
    @13
    omex
    @10
    cA
    @1
    crn
    #
    cvv
    @10
    @2
    @0
    cA
    @1
    wfo
    @21
    cA
    wceq
    @2
    @5
    simpl
    #
    @0
    cA
    @1
    f1ofo
    @0
    cA
    @1
    forn
    3syl
    @1
    vf
    vex
    rnex
    syl6eqelr
    #
    com
    cA
    cvv
    cvv
    xpexg
    sylancr
    @10
    vy
    vx
    cA
    @4
    vg
    vn
    vk
    @1
    @18
    @19
    cvv
    @23
    @2
    @5
    simpr
    @22
    @18
    eqid
    @19
    eqid
    fseqenlem2
    @7
    @8
    cvv
    @19
    f1domg
    sylc
    @10
    @20
    @12
    @23
    cA
    vn
    cvv
    fseqdom
    syl
    @7
    @8
    sbth
    syl2anc
    exlimivv
    sylbir
    syl2anb
end
