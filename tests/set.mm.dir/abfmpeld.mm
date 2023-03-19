include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wb.mm"
include "wsbc.mm"
include "cab.mm"
include "csb.mm"
include "cvv.mm"
include "wceq.mm"
include "wal.mm"
include "alrimiv.mm"
include "csbexg.mm"
include "syl.mm"
include "fvmpts.mm"
include "sylan2.mm"
include "csbab.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "adantl.mm"
include "cv.mm"
include "wi.mm"
include "simpll.mm"
include "ancomsd.mm"
include "impl.mm"
include "sbcied.mm"
include "ex.mm"
include "elabgt.mm"
include "bitrd.mm"
include "an13s.mm"

theorem abfmpeld
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  assume abfmpeld.1: |- F = ( x e. V |-> { y | ps } )
  assume abfmpeld.2: |- ( ph -> { y | ps } e. _V )
  assume abfmpeld.3: |- ( ph -> ( ( x = A /\ y = B ) -> ( ps <-> ch ) ) )

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
  disjoint ch x
  disjoint ch y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( ( A e. V /\ B e. W ) -> ( B e. ( F ` A ) <-> ch ) ) )

  proof
    wph
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
    wch
    wb
    #
    @1
    @0
    wph
    @4
    @1
    @0
    wph
    wa
    #
    wa
    @3
    cB
    wps
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    wcel
    #
    wch
    @5
    @3
    @8
    wb
    @1
    @5
    @2
    @7
    cB
    @5
    @2
    vx
    cA
    wps
    vy
    cab
    #
    csb
    #
    @7
    wph
    @0
    @10
    cvv
    wcel
    #
    @2
    @10
    wceq
    wph
    @9
    cvv
    wcel
    #
    vx
    wal
    @11
    wph
    @12
    vx
    abfmpeld.2
    alrimiv
    vx
    cA
    @9
    cvv
    csbexg
    syl
    vx
    cA
    @9
    cV
    cF
    cvv
    abfmpeld.1
    fvmpts
    sylan2
    wps
    vx
    vy
    cA
    csbab
    syl6eq
    eleq2d
    adantl
    @5
    @1
    vy
    cv
    cB
    wceq
    #
    @6
    wch
    wb
    #
    wi
    #
    vy
    wal
    @8
    wch
    wb
    @5
    @15
    vy
    @5
    @13
    @14
    @5
    @13
    wa
    wps
    wch
    vx
    cA
    cV
    @0
    wph
    @13
    simpll
    @5
    @13
    vx
    cv
    cA
    wceq
    #
    wps
    wch
    wb
    #
    wph
    @13
    @16
    wa
    @17
    wi
    @0
    wph
    @16
    @13
    @17
    abfmpeld.3
    ancomsd
    adantl
    impl
    sbcied
    ex
    alrimiv
    @6
    wch
    vy
    cB
    cW
    elabgt
    sylan2
    bitrd
    an13s
    ex
end
