include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "nfeq.mm"
include "eleq2.mm"
include "imbi1d.mm"
include "albid.mm"
include "df-ral.mm"
include "3bitr4g.mm"

theorem raleqf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleq1f.1: |- F/_ x A
  assume raleq1f.2: |- F/_ x B


  assert |- ( A = B -> ( A. x e. A ph <-> A. x e. B ph ) )

  proof
    cA
    cB
    wceq
    #
    vx
    cv
    #
    cA
    wcel
    #
    wph
    wi
    #
    vx
    wal
    @1
    cB
    wcel
    #
    wph
    wi
    #
    vx
    wal
    wph
    vx
    cA
    wral
    wph
    vx
    cB
    wral
    @0
    @3
    @5
    vx
    vx
    cA
    cB
    raleq1f.1
    raleq1f.2
    nfeq
    @0
    @2
    @4
    wph
    cA
    cB
    @1
    eleq2
    imbi1d
    albid
    wph
    vx
    cA
    df-ral
    wph
    vx
    cB
    df-ral
    3bitr4g
end
