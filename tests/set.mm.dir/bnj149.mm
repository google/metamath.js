include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c1o.mm"
include "wfn.mm"
include "w3a.mm"
include "wmo.mm"
include "wi.mm"
include "c0.mm"
include "c-bnj14.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "wal.mm"
include "wf.mm"
include "cfv.mm"
include "wral.mm"
include "simpr1.mm"
include "df1o2.mm"
include "fneq2i.mm"
include "sylib.mm"
include "simpr2.mm"
include "fvex.mm"
include "elsn.mm"
include "sylibr.mm"
include "0ex.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "ralsn.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "cvv.mm"
include "wb.mm"
include "bnj93.mm"
include "adantr.mm"
include "fsng.mm"
include "sylancr.mm"
include "mpbid.mm"
include "ex.mm"
include "alrimiv.mm"
include "mo2icl.mm"
include "syl.mm"
include "mpbir.mm"

theorem bnj149
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwze0: wff ze0
  let bnjwph1: wff ph1
  let bnjwps1: wff ps1
  let bnjwth1: wff th1
  let bnjwze1: wff ze1
  assume bnj149.1: |- ( th1 <-> ( ( R _FrSe A /\ x e. A ) -> E* f ( f Fn 1o /\ ph' /\ ps' ) ) )
  assume bnj149.2: |- ( ze0 <-> ( f Fn 1o /\ ph' /\ ps' ) )
  assume bnj149.3: |- ( ze1 <-> [. g / f ]. ze0 )
  assume bnj149.4: |- ( ph1 <-> [. g / f ]. ph' )
  assume bnj149.5: |- ( ps1 <-> [. g / f ]. ps' )
  assume bnj149.6: |- ( ph' <-> ( f ` (/) ) = _pred ( x , A , R ) )

  disjoint A f
  disjoint A g
  disjoint A x
  disjoint f g
  disjoint f x
  disjoint g x
  disjoint R f
  disjoint R g
  disjoint R x
  disjoint f ze1
  disjoint g ze0
  assert |- th1

  proof
    bnjwth1
    cA
    cR
    w-bnj15
    vx
    cv
    #
    cA
    wcel
    wa
    #
    vf
    cv
    #
    c1o
    wfn
    #
    bnjwphm
    bnjwpsm
    w3a
    #
    vf
    wmo
    #
    wi
    @1
    @4
    @2
    c0
    cA
    cR
    @0
    c-bnj14
    #
    cop
    csn
    #
    wceq
    #
    wi
    #
    vf
    wal
    @5
    @1
    @9
    vf
    @1
    @4
    @8
    @1
    @4
    wa
    #
    c0
    csn
    #
    @6
    csn
    #
    @2
    wf
    #
    @8
    @10
    @2
    @11
    wfn
    #
    vg
    cv
    #
    @2
    cfv
    #
    @12
    wcel
    #
    vg
    @11
    wral
    #
    @13
    @10
    @3
    @14
    @1
    @3
    bnjwphm
    bnjwpsm
    simpr1
    c1o
    @11
    @2
    df1o2
    fneq2i
    sylib
    @10
    c0
    @2
    cfv
    #
    @12
    wcel
    #
    @18
    @10
    @19
    @6
    wceq
    #
    @20
    @10
    bnjwphm
    @21
    @1
    @3
    bnjwphm
    bnjwpsm
    simpr2
    bnj149.6
    sylib
    @19
    @6
    c0
    @2
    fvex
    elsn
    sylibr
    @17
    @20
    vg
    c0
    0ex
    @15
    c0
    wceq
    @16
    @19
    @12
    @15
    c0
    @2
    fveq2
    eleq1d
    ralsn
    sylibr
    vg
    @11
    @12
    @2
    ffnfv
    sylanbrc
    @10
    c0
    cvv
    wcel
    @6
    cvv
    wcel
    #
    @13
    @8
    wb
    0ex
    @1
    @22
    @4
    vx
    cA
    cR
    bnj93
    adantr
    c0
    @6
    cvv
    cvv
    @2
    fsng
    sylancr
    mpbid
    ex
    alrimiv
    @4
    vf
    @7
    mo2icl
    syl
    bnj149.1
    mpbir
end
