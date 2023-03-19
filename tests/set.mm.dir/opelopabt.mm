include "cop.mm"
include "copab.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "elopab.mm"
include "19.26-2.mm"
include "prth.mm"
include "bitr.mm"
include "syl6.mm"
include "2alimi.mm"
include "sylbir.mm"
include "copsex2t.mm"
include "stoic3.mm"
include "syl5bb.mm"

theorem opelopabt
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ch x
  disjoint ch y
  assert |- ( ( A. x A. y ( x = A -> ( ph <-> ps ) ) /\ A. x A. y ( y = B -> ( ps <-> ch ) ) /\ ( A e. V /\ B e. W ) ) -> ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) )

  proof
    cA
    cB
    cop
    #
    wph
    vx
    vy
    copab
    wcel
    @0
    vx
    cv
    #
    vy
    cv
    #
    cop
    wceq
    wph
    wa
    vy
    wex
    vx
    wex
    #
    @1
    cA
    wceq
    #
    wph
    wps
    wb
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @2
    cB
    wceq
    #
    wps
    wch
    wb
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    w3a
    wch
    wph
    vx
    vy
    @0
    elopab
    @7
    @11
    @4
    @8
    wa
    #
    wph
    wch
    wb
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @12
    @3
    wch
    wb
    @7
    @11
    wa
    @6
    @10
    wa
    #
    vy
    wal
    vx
    wal
    @16
    @6
    @10
    vx
    vy
    19.26-2
    @17
    @15
    vx
    vy
    @17
    @13
    @5
    @9
    wa
    @14
    @4
    @5
    @8
    @9
    prth
    wph
    wps
    wch
    bitr
    syl6
    2alimi
    sylbir
    wph
    wch
    vx
    vy
    cA
    cB
    cV
    cW
    copsex2t
    stoic3
    syl5bb
end
