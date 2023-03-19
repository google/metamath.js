include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wsbc.mm"
include "cab.mm"
include "wb.mm"
include "csb.mm"
include "cvv.mm"
include "wceq.mm"
include "csbex.mm"
include "fvmpts.mm"
include "mpan2.mm"
include "csbab.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "adantr.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "simpl.mm"
include "ancoms.mm"
include "adantll.mm"
include "sbcied.mm"
include "ex.mm"
include "alrimiv.mm"
include "elabgt.mm"
include "sylan2.mm"
include "bitrd.mm"

theorem abfmpel
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  assume abfmpel.1: |- F = ( x e. V |-> { y | ph } )
  assume abfmpel.2: |- { y | ph } e. _V
  assume abfmpel.3: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint V x
  disjoint V y
  disjoint W y
  disjoint ps x
  disjoint ps y
  assert |- ( ( A e. V /\ B e. W ) -> ( B e. ( F ` A ) <-> ps ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    cB
    cA
    cF
    cfv
    #
    wcel
    #
    cB
    wph
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    wcel
    #
    wps
    @0
    @3
    @6
    wb
    @1
    @0
    @2
    @5
    cB
    @0
    @2
    vx
    cA
    wph
    vy
    cab
    #
    csb
    #
    @5
    @0
    @8
    cvv
    wcel
    @2
    @8
    wceq
    vx
    cA
    @7
    abfmpel.2
    csbex
    vx
    cA
    @7
    cV
    cF
    cvv
    abfmpel.1
    fvmpts
    mpan2
    wph
    vx
    vy
    cA
    csbab
    syl6eq
    eleq2d
    adantr
    @1
    @0
    @6
    wps
    wb
    #
    @0
    @1
    vy
    cv
    cB
    wceq
    #
    @4
    wps
    wb
    #
    wi
    #
    vy
    wal
    @9
    @0
    @12
    vy
    @0
    @10
    @11
    @0
    @10
    wa
    wph
    wps
    vx
    cA
    cV
    @0
    @10
    simpl
    @10
    vx
    cv
    cA
    wceq
    #
    wph
    wps
    wb
    #
    @0
    @13
    @10
    @14
    abfmpel.3
    ancoms
    adantll
    sbcied
    ex
    alrimiv
    @4
    wps
    vy
    cB
    cW
    elabgt
    sylan2
    ancoms
    bitrd
end
