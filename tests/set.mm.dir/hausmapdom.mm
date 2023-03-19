include "cha.mm"
include "wcel.mm"
include "c1stc.mm"
include "wss.mm"
include "w3a.mm"
include "ccl.mm"
include "cfv.mm"
include "clm.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cima.mm"
include "cdom.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "wf.mm"
include "wb.mm"
include "1stcelcls.mm"
include "3adant1.mm"
include "cvv.mm"
include "cuni.mm"
include "uniexg.mm"
include "3ad2ant1.mm"
include "syl5eqel.mm"
include "simp3.mm"
include "ssexd.mm"
include "nnex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "bitr4d.mm"
include "df-rex.mm"
include "syl6bbr.mm"
include "vex.mm"
include "elima.mm"
include "eqrdv.mm"
include "wfun.mm"
include "ovex.mm"
include "lmfun.mm"
include "imadomg.mm"
include "mpsyl.mm"
include "eqbrtrd.mm"

theorem hausmapdom
  let cA: class A
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume hauspwdom.1: |- X = U. J


  assert |- ( ( J e. Haus /\ J e. 1stc /\ A C_ X ) -> ( ( cls ` J ) ` A ) ~<_ ( A ^m NN ) )

  proof
    cJ
    cha
    wcel
    #
    cJ
    c1stc
    wcel
    #
    cA
    cX
    wss
    #
    w3a
    #
    cA
    cJ
    ccl
    cfv
    cfv
    #
    cJ
    clm
    cfv
    #
    cA
    cn
    cmap
    co
    #
    cima
    #
    @6
    cdom
    @3
    vx
    @4
    @7
    @3
    vx
    cv
    #
    @4
    wcel
    #
    vf
    cv
    #
    @8
    @5
    wbr
    #
    vf
    @6
    wrex
    #
    @8
    @7
    wcel
    @3
    @9
    @10
    @6
    wcel
    #
    @11
    wa
    #
    vf
    wex
    #
    @12
    @3
    @9
    cn
    cA
    @10
    wf
    #
    @11
    wa
    #
    vf
    wex
    #
    @15
    @1
    @2
    @9
    @18
    wb
    @0
    @8
    cA
    vf
    cJ
    cX
    hauspwdom.1
    1stcelcls
    3adant1
    @3
    @14
    @17
    vf
    @3
    @13
    @16
    @11
    @3
    cA
    cvv
    wcel
    cn
    cvv
    wcel
    @13
    @16
    wb
    @3
    cA
    cX
    cvv
    @3
    cX
    cJ
    cuni
    #
    cvv
    hauspwdom.1
    @0
    @1
    @19
    cvv
    wcel
    @2
    cJ
    cha
    uniexg
    3ad2ant1
    syl5eqel
    @0
    @1
    @2
    simp3
    ssexd
    nnex
    cA
    cn
    @10
    cvv
    cvv
    elmapg
    sylancl
    anbi1d
    exbidv
    bitr4d
    @11
    vf
    @6
    df-rex
    syl6bbr
    vf
    @8
    @5
    @6
    vx
    vex
    elima
    syl6bbr
    eqrdv
    @6
    cvv
    wcel
    @3
    @5
    wfun
    #
    @7
    @6
    cdom
    wbr
    cA
    cn
    cmap
    ovex
    @0
    @1
    @20
    @2
    cJ
    lmfun
    3ad2ant1
    @6
    cvv
    @5
    imadomg
    mpsyl
    eqbrtrd
end
