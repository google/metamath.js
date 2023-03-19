include "cuni.mm"
include "cv.mm"
include "cima.mm"
include "cdif.mm"
include "wss.mm"
include "unissb.mm"
include "wcel.mm"
include "wa.mm"
include "abeq2i.mm"
include "wi.mm"
include "difss2.mm"
include "ssconb.mm"
include "exbiri.mm"
include "syl5.mm"
include "pm2.43d.mm"
include "imp.mm"
include "sylbi.mm"
include "elssuni.mm"
include "imass2.mm"
include "sscon.mm"
include "3syl.mm"
include "sstrd.mm"
include "mprgbir.mm"

theorem sbthlem1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  assume sbthlem.1: |- A e. _V
  assume sbthlem.2: |- D = { x | ( x C_ A /\ ( g " ( B \ ( f " x ) ) ) C_ ( A \ x ) ) }

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint f x
  disjoint g x
  assert |- U. D C_ ( A \ ( g " ( B \ ( f " U. D ) ) ) )

  proof
    cD
    cuni
    #
    cA
    vg
    cv
    #
    cB
    vf
    cv
    #
    @0
    cima
    #
    cdif
    #
    cima
    #
    cdif
    #
    wss
    vx
    cv
    #
    @6
    wss
    vx
    cD
    vx
    cD
    @6
    unissb
    @7
    cD
    wcel
    #
    @7
    cA
    @1
    cB
    @2
    @7
    cima
    #
    cdif
    #
    cima
    #
    cdif
    #
    @6
    @8
    @7
    cA
    wss
    #
    @11
    cA
    @7
    cdif
    wss
    #
    wa
    #
    @7
    @12
    wss
    #
    @15
    vx
    cD
    sbthlem.2
    abeq2i
    @13
    @14
    @16
    @13
    @14
    @16
    @14
    @11
    cA
    wss
    #
    @13
    @14
    @16
    wi
    @11
    cA
    @7
    difss2
    @13
    @17
    @16
    @14
    @7
    @11
    cA
    ssconb
    exbiri
    syl5
    pm2.43d
    imp
    sylbi
    @8
    @4
    @10
    wss
    #
    @5
    @11
    wss
    @12
    @6
    wss
    @8
    @7
    @0
    wss
    @9
    @3
    wss
    @18
    @7
    cD
    elssuni
    @7
    @0
    @2
    imass2
    @9
    @3
    cB
    sscon
    3syl
    @4
    @10
    @1
    imass2
    @5
    @11
    cA
    sscon
    3syl
    sstrd
    mprgbir
end
