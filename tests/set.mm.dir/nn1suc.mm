include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "wceq.mm"
include "cmin.mm"
include "co.mm"
include "wi.mm"
include "wsbc.mm"
include "1ex.mm"
include "sbcie.mm"
include "mpbir.mm"
include "wb.mm"
include "1nn.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "sbcieg.mm"
include "syl.mm"
include "dfsbcq.mm"
include "bitr3d.mm"
include "a1i.mm"
include "caddc.mm"
include "cv.mm"
include "ovex.mm"
include "oveq1.mm"
include "sbceq1d.mm"
include "syl5bbr.mm"
include "vtoclga.mm"
include "cc.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "bitrd.mm"
include "syl5ib.mm"
include "nn1m1nn.mm"
include "mpjaod.mm"

theorem nn1suc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nn1suc.1: |- ( x = 1 -> ( ph <-> ps ) )
  assume nn1suc.3: |- ( x = ( y + 1 ) -> ( ph <-> ch ) )
  assume nn1suc.4: |- ( x = A -> ( ph <-> th ) )
  assume nn1suc.5: |- ps
  assume nn1suc.6: |- ( y e. NN -> ch )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ph y
  assert |- ( A e. NN -> th )

  proof
    cA
    cn
    wcel
    #
    cA
    c1
    wceq
    #
    wth
    cA
    c1
    cmin
    co
    #
    cn
    wcel
    #
    @1
    wth
    wi
    @0
    @1
    wth
    wph
    vx
    c1
    wsbc
    #
    @4
    wps
    nn1suc.5
    wph
    wps
    vx
    c1
    1ex
    nn1suc.1
    sbcie
    mpbir
    @1
    wph
    vx
    cA
    wsbc
    #
    wth
    @4
    @1
    @0
    @5
    wth
    wb
    @1
    @0
    c1
    cn
    wcel
    1nn
    cA
    c1
    cn
    eleq1
    mpbiri
    wph
    wth
    vx
    cA
    cn
    nn1suc.4
    sbcieg
    #
    syl
    wph
    vx
    cA
    c1
    dfsbcq
    bitr3d
    mpbiri
    a1i
    @3
    wph
    vx
    @2
    c1
    caddc
    co
    #
    wsbc
    #
    @0
    wth
    wch
    @8
    vy
    @2
    cn
    wch
    wph
    vx
    vy
    cv
    #
    c1
    caddc
    co
    #
    wsbc
    @9
    @2
    wceq
    #
    @8
    wph
    wch
    vx
    @10
    @9
    c1
    caddc
    ovex
    nn1suc.3
    sbcie
    @11
    wph
    vx
    @10
    @7
    @9
    @2
    c1
    caddc
    oveq1
    sbceq1d
    syl5bbr
    nn1suc.6
    vtoclga
    @0
    @8
    @5
    wth
    @0
    wph
    vx
    @7
    cA
    @0
    cA
    cc
    wcel
    c1
    cc
    wcel
    @7
    cA
    wceq
    cA
    nncn
    ax-1cn
    cA
    c1
    npcan
    sylancl
    sbceq1d
    @6
    bitrd
    syl5ib
    cA
    nn1m1nn
    mpjaod
end
