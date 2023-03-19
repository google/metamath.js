include "wsbc.mm"
include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c1o.mm"
include "wfn.mm"
include "w3a.mm"
include "wi.mm"
include "sbcbii.mm"
include "cvv.mm"
include "wb.mm"
include "bnj95.mm"
include "nfv.mm"
include "sbc19.21g.mm"
include "ax-mp.mm"
include "fneq1.mm"
include "sbcie2g.mm"
include "bicomi.mm"
include "bnj206.mm"
include "imbi2i.mm"
include "3bitri.mm"
include "bitri.mm"

theorem bnj124
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vf: setvar f
  let cF: class F
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwzem: wff ze'
  let bnjwphn: wff ph"
  let bnjwpsn: wff ps"
  let bnjwzen: wff ze"
  let vz: setvar z
  assume bnj124.1: |- F = { <. (/) , _pred ( x , A , R ) >. }
  assume bnj124.2: |- ( ph" <-> [. F / f ]. ph' )
  assume bnj124.3: |- ( ps" <-> [. F / f ]. ps' )
  assume bnj124.4: |- ( ze" <-> [. F / f ]. ze' )
  assume bnj124.5: |- ( ze' <-> ( ( R _FrSe A /\ x e. A ) -> ( f Fn 1o /\ ph' /\ ps' ) ) )

  disjoint A f
  disjoint R f
  disjoint f x
  disjoint f z
  disjoint x z
  disjoint F z
  assert |- ( ze" <-> ( ( R _FrSe A /\ x e. A ) -> ( F Fn 1o /\ ph" /\ ps" ) ) )

  proof
    bnjwzen
    bnjwzem
    vf
    cF
    wsbc
    #
    cA
    cR
    w-bnj15
    vx
    cv
    cA
    wcel
    wa
    #
    cF
    c1o
    wfn
    #
    bnjwphn
    bnjwpsn
    w3a
    #
    wi
    #
    bnj124.4
    @0
    @1
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
    wi
    #
    vf
    cF
    wsbc
    #
    @1
    @7
    vf
    cF
    wsbc
    #
    wi
    #
    @4
    bnjwzem
    @8
    vf
    cF
    bnj124.5
    sbcbii
    cF
    cvv
    wcel
    #
    @9
    @11
    wb
    vx
    cA
    cR
    cF
    bnj124.1
    bnj95
    #
    @1
    @7
    vf
    cF
    cvv
    @1
    vf
    nfv
    sbc19.21g
    ax-mp
    @10
    @3
    @1
    @6
    bnjwphm
    bnjwpsm
    vf
    cF
    @2
    bnjwphn
    bnjwpsn
    @6
    vf
    cF
    wsbc
    #
    @2
    @12
    @14
    @2
    wb
    @13
    @6
    vz
    cv
    #
    c1o
    wfn
    @2
    vf
    vz
    cF
    cvv
    c1o
    @5
    @15
    fneq1
    c1o
    @15
    cF
    fneq1
    sbcie2g
    ax-mp
    bicomi
    bnj124.2
    bnj124.3
    @13
    bnj206
    imbi2i
    3bitri
    bitri
end
