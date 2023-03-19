include "cuni.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "c0.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wf.mm"
include "wex.mm"
include "cvv.mm"
include "wwe.mm"
include "uniexr.mm"
include "dfac8b.mm"
include "dfac8c.mm"
include "sylc.mm"
include "adantr.mm"
include "cmpt.mm"
include "nelne2.mm"
include "ancoms.mm"
include "adantll.mm"
include "pm2.27.mm"
include "syl.mm"
include "ralimdva.mm"
include "imp.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "elunii.mm"
include "sylancom.mm"
include "eqid.mm"
include "fmptd.mm"
include "ad2antrr.mm"
include "elex.mm"
include "fex2.mm"
include "syl3anc.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eleq1d.mm"
include "ralbiia.mm"
include "sylibr.mm"
include "jca.mm"
include "feq1.mm"
include "fveq1.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "exlimddv.mm"

theorem ac5num
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  let vy: setvar y

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint f g
  disjoint f r
  disjoint f y
  disjoint g r
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A y
  assert |- ( ( U. A e. dom card /\ -. (/) e. A ) -> E. f ( f : A --> U. A /\ A. x e. A ( f ` x ) e. x ) )

  proof
    cA
    cuni
    #
    ccrd
    cdm
    #
    wcel
    #
    c0
    cA
    wcel
    wn
    #
    wa
    #
    vx
    cv
    #
    c0
    wne
    #
    @5
    vg
    cv
    #
    cfv
    #
    @5
    wcel
    #
    wi
    #
    vx
    cA
    wral
    #
    cA
    @0
    vf
    cv
    #
    wf
    #
    @5
    @12
    cfv
    #
    @5
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    vg
    @2
    @11
    vg
    wex
    #
    @3
    @2
    cA
    cvv
    wcel
    #
    @0
    vr
    cv
    wwe
    vr
    wex
    @19
    cA
    @1
    uniexr
    #
    vr
    @0
    dfac8b
    vx
    cA
    cvv
    vg
    vr
    dfac8c
    sylc
    adantr
    @4
    @11
    wa
    #
    vy
    cA
    vy
    cv
    #
    @7
    cfv
    #
    cmpt
    #
    cvv
    wcel
    #
    cA
    @0
    @25
    wf
    #
    @5
    @25
    cfv
    #
    @5
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    @18
    @22
    @27
    @20
    @0
    cvv
    wcel
    #
    @26
    @22
    vy
    cA
    @24
    @0
    @25
    @22
    @23
    cA
    wcel
    #
    @24
    @23
    wcel
    #
    @24
    @0
    wcel
    @22
    @9
    vx
    cA
    wral
    #
    @33
    @34
    @4
    @11
    @35
    @4
    @10
    @9
    vx
    cA
    @4
    @5
    cA
    wcel
    #
    wa
    @6
    @10
    @9
    wi
    @3
    @36
    @6
    @2
    @36
    @3
    @6
    @5
    c0
    cA
    nelne2
    ancoms
    adantll
    @6
    @9
    pm2.27
    syl
    ralimdva
    imp
    #
    @9
    @34
    vx
    @23
    cA
    @5
    @23
    wceq
    #
    @8
    @24
    @5
    @23
    @5
    @23
    @7
    fveq2
    @38
    id
    eleq12d
    rspccva
    sylan
    @24
    @23
    cA
    elunii
    sylancom
    @25
    eqid
    #
    fmptd
    #
    @2
    @20
    @3
    @11
    @21
    ad2antrr
    @2
    @32
    @3
    @11
    @0
    @1
    elex
    ad2antrr
    cA
    @0
    @25
    cvv
    cvv
    fex2
    syl3anc
    @22
    @27
    @30
    @40
    @22
    @35
    @30
    @37
    @29
    @9
    vx
    cA
    @36
    @28
    @8
    @5
    vy
    @5
    @24
    @8
    cA
    @25
    @23
    @5
    @7
    fveq2
    @39
    @5
    @7
    fvex
    fvmpt
    eleq1d
    ralbiia
    sylibr
    jca
    @17
    @31
    vf
    @25
    cvv
    @12
    @25
    wceq
    #
    @13
    @27
    @16
    @30
    cA
    @0
    @12
    @25
    feq1
    @41
    @15
    @29
    vx
    cA
    @41
    @14
    @28
    @5
    @5
    @12
    @25
    fveq1
    eleq1d
    ralbidv
    anbi12d
    spcegv
    sylc
    exlimddv
end
