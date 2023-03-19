include "c0.mm"
include "wceq.mm"
include "wral.mm"
include "wb.mm"
include "rzal.mm"
include "2thd.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "neq0.mm"
include "wi.mm"
include "biimt.mm"
include "wal.mm"
include "df-ral.mm"
include "nfra1.mm"
include "19.23.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "sylbi.mm"
include "pm2.61i.mm"

theorem ralidm
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A. x e. A A. x e. A ph <-> A. x e. A ph )

  proof
    cA
    c0
    wceq
    #
    wph
    vx
    cA
    wral
    #
    vx
    cA
    wral
    #
    @1
    wb
    #
    @0
    @2
    @1
    @1
    vx
    cA
    rzal
    wph
    vx
    cA
    rzal
    2thd
    @0
    wn
    vx
    cv
    cA
    wcel
    #
    vx
    wex
    #
    @3
    vx
    cA
    neq0
    @5
    @1
    @5
    @1
    wi
    #
    @2
    @5
    @1
    biimt
    @2
    @4
    @1
    wi
    vx
    wal
    @6
    @1
    vx
    cA
    df-ral
    @4
    @1
    vx
    wph
    vx
    cA
    nfra1
    19.23
    bitri
    syl6rbbr
    sylbi
    pm2.61i
end
