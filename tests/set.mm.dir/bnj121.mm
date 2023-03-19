include "c1o.mm"
include "wsbc.mm"
include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "w3a.mm"
include "wi.mm"
include "sbcbii.mm"
include "bnj105.mm"
include "bnj90.mm"
include "bicomi.mm"
include "3anbi123i.mm"
include "sbc3an.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "cvv.mm"
include "wb.mm"
include "nfv.mm"
include "sbc19.21g.mm"
include "ax-mp.mm"
include "3bitr4i.mm"

theorem bnj121
  let wph: wff ph
  let wps: wff ps
  let wze: wff ze
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vn: setvar n
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwzem: wff ze'
  assume bnj121.1: |- ( ze <-> ( ( R _FrSe A /\ x e. A ) -> ( f Fn n /\ ph /\ ps ) ) )
  assume bnj121.2: |- ( ze' <-> [. 1o / n ]. ze )
  assume bnj121.3: |- ( ph' <-> [. 1o / n ]. ph )
  assume bnj121.4: |- ( ps' <-> [. 1o / n ]. ps )

  disjoint A n
  disjoint R n
  disjoint f n
  disjoint n x
  assert |- ( ze' <-> ( ( R _FrSe A /\ x e. A ) -> ( f Fn 1o /\ ph' /\ ps' ) ) )

  proof
    wze
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
    wi
    #
    vn
    c1o
    wsbc
    #
    bnjwzem
    @0
    @1
    c1o
    wfn
    #
    bnjwphm
    bnjwpsm
    w3a
    #
    wi
    #
    wze
    @4
    vn
    c1o
    bnj121.1
    sbcbii
    bnj121.2
    @8
    @0
    @3
    vn
    c1o
    wsbc
    #
    wi
    #
    @5
    @7
    @9
    @0
    @7
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
    @9
    @6
    @11
    bnjwphm
    @12
    bnjwpsm
    @13
    @11
    @6
    vn
    vf
    c1o
    bnj105
    bnj90
    bicomi
    bnj121.3
    bnj121.4
    3anbi123i
    @2
    wph
    wps
    vn
    c1o
    sbc3an
    bitr4i
    imbi2i
    c1o
    cvv
    wcel
    @5
    @10
    wb
    bnj105
    @0
    @3
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
