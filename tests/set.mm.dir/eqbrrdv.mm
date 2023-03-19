include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wbr.mm"
include "df-br.mm"
include "3bitr3g.mm"
include "alrimivv.mm"
include "wrel.mm"
include "eqrel.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem eqbrrdv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume eqbrrdv.1: |- ( ph -> Rel A )
  assume eqbrrdv.2: |- ( ph -> Rel B )
  assume eqbrrdv.3: |- ( ph -> ( x A y <-> x B y ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cB
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    wb
    #
    vy
    wal
    vx
    wal
    #
    wph
    @6
    vx
    vy
    wph
    @1
    @2
    cA
    wbr
    @1
    @2
    cB
    wbr
    @4
    @5
    eqbrrdv.3
    @1
    @2
    cA
    df-br
    @1
    @2
    cB
    df-br
    3bitr3g
    alrimivv
    wph
    cA
    wrel
    cB
    wrel
    @0
    @7
    wb
    eqbrrdv.1
    eqbrrdv.2
    vx
    vy
    cA
    cB
    eqrel
    syl2anc
    mpbird
end
