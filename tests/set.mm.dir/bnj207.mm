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
include "cvv.mm"
include "wb.mm"
include "nfv.mm"
include "sbc19.21g.mm"
include "ax-mp.mm"
include "bnj89.mm"
include "bnj90.mm"
include "bicomi.mm"
include "bnj206.mm"
include "eubii.mm"
include "bitri.mm"
include "imbi2i.mm"

theorem bnj207
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vn: setvar n
  let cM: class M
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  assume bnj207.1: |- ( ch <-> ( ( R _FrSe A /\ x e. A ) -> E! f ( f Fn n /\ ph /\ ps ) ) )
  assume bnj207.2: |- ( ph' <-> [. M / n ]. ph )
  assume bnj207.3: |- ( ps' <-> [. M / n ]. ps )
  assume bnj207.4: |- ( ch' <-> [. M / n ]. ch )
  assume bnj207.5: |- M e. _V

  disjoint A n
  disjoint M f
  disjoint R n
  disjoint f n
  disjoint n x
  assert |- ( ch' <-> ( ( R _FrSe A /\ x e. A ) -> E! f ( f Fn M /\ ph' /\ ps' ) ) )

  proof
    bnjwchm
    wch
    vn
    cM
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
    vf
    cv
    #
    cM
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
    bnj207.4
    @0
    @1
    @2
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
    cM
    wsbc
    #
    @6
    wch
    @10
    vn
    cM
    bnj207.1
    sbcbii
    @11
    @1
    @9
    vn
    cM
    wsbc
    #
    wi
    #
    @6
    cM
    cvv
    wcel
    @11
    @13
    wb
    bnj207.5
    @1
    @9
    vn
    cM
    cvv
    @1
    vn
    nfv
    sbc19.21g
    ax-mp
    @12
    @5
    @1
    @12
    @8
    vn
    cM
    wsbc
    #
    vf
    weu
    @5
    @8
    vf
    vn
    cM
    bnj207.5
    bnj89
    @14
    @4
    vf
    @7
    wph
    wps
    vn
    cM
    @3
    bnjwphm
    bnjwpsm
    @7
    vn
    cM
    wsbc
    @3
    vn
    vf
    cM
    bnj207.5
    bnj90
    bicomi
    bnj207.2
    bnj207.3
    bnj207.5
    bnj206
    eubii
    bitri
    imbi2i
    bitri
    bitri
    bitri
end
