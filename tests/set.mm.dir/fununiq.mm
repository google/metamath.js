include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "dffun2.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "wb.mm"
include "breq12.mm"
include "3adant3.mm"
include "3adant2.mm"
include "anbi12d.mm"
include "eqeq12.mm"
include "3adant1.mm"
include "imbi12d.mm"
include "spc3gv.mm"
include "mp3an.mm"
include "adantl.mm"
include "sylbi.mm"

theorem fununiq
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume fununiq.1: |- A e. _V
  assume fununiq.2: |- B e. _V
  assume fununiq.3: |- C e. _V


  assert |- ( Fun F -> ( ( A F B /\ A F C ) -> B = C ) )

  proof
    cF
    wfun
    cF
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    @1
    vz
    cv
    #
    cF
    wbr
    #
    wa
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    wal
    vy
    wal
    vx
    wal
    #
    wa
    cA
    cB
    cF
    wbr
    #
    cA
    cC
    cF
    wbr
    #
    wa
    #
    cB
    cC
    wceq
    #
    wi
    #
    vx
    vy
    vz
    cF
    dffun2
    @9
    @14
    @0
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cC
    cvv
    wcel
    @9
    @14
    wi
    fununiq.1
    fununiq.2
    fununiq.3
    @8
    @14
    vx
    vy
    vz
    cA
    cB
    cC
    cvv
    cvv
    cvv
    @1
    cA
    wceq
    #
    @2
    cB
    wceq
    #
    @4
    cC
    wceq
    #
    w3a
    #
    @6
    @12
    @7
    @13
    @18
    @3
    @10
    @5
    @11
    @15
    @16
    @3
    @10
    wb
    @17
    @1
    cA
    @2
    cB
    cF
    breq12
    3adant3
    @15
    @17
    @5
    @11
    wb
    @16
    @1
    cA
    @4
    cC
    cF
    breq12
    3adant2
    anbi12d
    @16
    @17
    @7
    @13
    wb
    @15
    @2
    cB
    @4
    cC
    eqeq12
    3adant1
    imbi12d
    spc3gv
    mp3an
    adantl
    sylbi
end
