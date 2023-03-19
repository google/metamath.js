include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cio.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "vex.mm"
include "wa.mm"
include "cop.mm"
include "elimasng.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "mpan2.mm"
include "iotabidv.mm"
include "df-fv.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "snprc.mm"
include "biimpi.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "weu.mm"
include "wex.mm"
include "noel.mm"
include "nex.mm"
include "euex.mm"
include "mto.mm"
include "iotanul.mm"
include "ax-mp.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem dffv3
  let vx: setvar x
  let cA: class A
  let cF: class F

  disjoint F x
  disjoint A x
  assert |- ( F ` A ) = ( iota x x e. ( F " { A } ) )

  proof
    cA
    cvv
    wcel
    #
    cA
    cF
    cfv
    #
    vx
    cv
    #
    cF
    cA
    csn
    #
    cima
    #
    wcel
    #
    vx
    cio
    #
    wceq
    @0
    @6
    cA
    @2
    cF
    wbr
    #
    vx
    cio
    @1
    @0
    @5
    @7
    vx
    @0
    @2
    cvv
    wcel
    #
    @5
    @7
    wb
    vx
    vex
    @0
    @8
    wa
    @5
    cA
    @2
    cop
    cF
    wcel
    @7
    cF
    cA
    @2
    cvv
    cvv
    elimasng
    cA
    @2
    cF
    df-br
    syl6bbr
    mpan2
    iotabidv
    vx
    cA
    cF
    df-fv
    syl6reqr
    @0
    wn
    #
    @1
    c0
    @6
    cA
    cF
    fvprc
    @9
    @6
    @2
    c0
    wcel
    #
    vx
    cio
    #
    c0
    @9
    @5
    @10
    vx
    @9
    @4
    c0
    @2
    @9
    @4
    cF
    c0
    cima
    c0
    @9
    @3
    c0
    cF
    @9
    @3
    c0
    wceq
    cA
    snprc
    biimpi
    imaeq2d
    cF
    ima0
    syl6eq
    eleq2d
    iotabidv
    @10
    vx
    weu
    #
    wn
    @11
    c0
    wceq
    @12
    @10
    vx
    wex
    @10
    vx
    @2
    noel
    nex
    @10
    vx
    euex
    mto
    @10
    vx
    iotanul
    ax-mp
    syl6eq
    eqtr4d
    pm2.61i
end
