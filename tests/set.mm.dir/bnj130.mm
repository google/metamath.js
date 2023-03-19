include "c1o.mm"
include "wsbc.mm"
include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "w3a.mm"
include "weu.mm"
include "wi.mm"
include "sbcbii.mm"
include "bnj105.mm"
include "bnj90.mm"
include "bicomi.mm"
include "3anbi123i.mm"
include "sbc3an.mm"
include "bitr4i.mm"
include "eubii.mm"
include "bnj89.mm"
include "imbi2i.mm"
include "cvv.mm"
include "wb.mm"
include "nfv.mm"
include "sbc19.21g.mm"
include "ax-mp.mm"
include "3bitr4i.mm"

theorem bnj130
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vn: setvar n
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwthm: wff th'
  assume bnj130.1: |- ( th <-> ( ( R _FrSe A /\ x e. A ) -> E! f ( f Fn n /\ ph /\ ps ) ) )
  assume bnj130.2: |- ( ph' <-> [. 1o / n ]. ph )
  assume bnj130.3: |- ( ps' <-> [. 1o / n ]. ps )
  assume bnj130.4: |- ( th' <-> [. 1o / n ]. th )

  disjoint A n
  disjoint R n
  disjoint f n
  disjoint n x
  assert |- ( th' <-> ( ( R _FrSe A /\ x e. A ) -> E! f ( f Fn 1o /\ ph' /\ ps' ) ) )

  proof
    wth
    vn
    c1o
    wsbc
    cA
    cR
    w-bnj15
    vx
    cv
    cA
    wcel
    wa
    #
    vf
    cv
    #
    vn
    cv
    wfn
    #
    wph
    wps
    w3a
    #
    vf
    weu
    #
    wi
    #
    vn
    c1o
    wsbc
    #
    bnjwthm
    @0
    @1
    c1o
    wfn
    #
    bnjwphm
    bnjwpsm
    w3a
    #
    vf
    weu
    #
    wi
    #
    wth
    @5
    vn
    c1o
    bnj130.1
    sbcbii
    bnj130.4
    @10
    @0
    @4
    vn
    c1o
    wsbc
    #
    wi
    #
    @6
    @9
    @11
    @0
    @9
    @3
    vn
    c1o
    wsbc
    #
    vf
    weu
    @11
    @8
    @13
    vf
    @8
    @2
    vn
    c1o
    wsbc
    #
    wph
    vn
    c1o
    wsbc
    #
    wps
    vn
    c1o
    wsbc
    #
    w3a
    @13
    @7
    @14
    bnjwphm
    @15
    bnjwpsm
    @16
    @14
    @7
    vn
    vf
    c1o
    bnj105
    bnj90
    bicomi
    bnj130.2
    bnj130.3
    3anbi123i
    @2
    wph
    wps
    vn
    c1o
    sbc3an
    bitr4i
    eubii
    @3
    vf
    vn
    c1o
    bnj105
    bnj89
    bitr4i
    imbi2i
    c1o
    cvv
    wcel
    @6
    @12
    wb
    bnj105
    @0
    @4
    vn
    c1o
    cvv
    @0
    vn
    nfv
    sbc19.21g
    ax-mp
    bitr4i
    3bitr4i
end
