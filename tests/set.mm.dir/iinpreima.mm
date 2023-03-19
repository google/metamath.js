include "wfun.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ccnv.mm"
include "ciin.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cdm.mm"
include "cfv.mm"
include "simpll.mm"
include "cnvimass.mm"
include "sseli.mm"
include "adantl.mm"
include "cvv.mm"
include "fvex.mm"
include "fvimacnvi.mm"
include "adantlr.mm"
include "eliin.mm"
include "biimpa.mm"
include "sylancr.mm"
include "fvimacnv.mm"
include "ralbidv.mm"
include "syl21anc.mm"
include "wb.mm"
include "vex.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "wi.mm"
include "biimpd.mm"
include "ex.mm"
include "ralimdv.mm"
include "sylc.mm"
include "wrex.mm"
include "r19.2zb.mm"
include "biimpi.mm"
include "rexlimivw.mm"
include "syl6.mm"
include "syl5bi.mm"
include "imp.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "impbida.mm"
include "eqrdv.mm"

theorem iinpreima
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint F x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F y
  assert |- ( ( Fun F /\ A =/= (/) ) -> ( `' F " |^|_ x e. A B ) = |^|_ x e. A ( `' F " B ) )

  proof
    cF
    wfun
    #
    cA
    c0
    wne
    #
    wa
    #
    vy
    cF
    ccnv
    #
    vx
    cA
    cB
    ciin
    #
    cima
    #
    vx
    cA
    @3
    cB
    cima
    #
    ciin
    #
    @2
    vy
    cv
    #
    @5
    wcel
    #
    @8
    @7
    wcel
    #
    @2
    @9
    wa
    #
    @8
    @6
    wcel
    #
    vx
    cA
    wral
    #
    @10
    @11
    @0
    @8
    cF
    cdm
    #
    wcel
    #
    @8
    cF
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @13
    @0
    @1
    @9
    simpll
    @9
    @15
    @2
    @5
    @14
    @8
    cF
    @4
    cnvimass
    sseli
    adantl
    @11
    @16
    cvv
    wcel
    #
    @16
    @4
    wcel
    #
    @18
    @8
    cF
    fvex
    #
    @0
    @9
    @20
    @1
    @8
    @4
    cF
    fvimacnvi
    adantlr
    @19
    @20
    @18
    vx
    @16
    cA
    cB
    cvv
    eliin
    #
    biimpa
    sylancr
    @0
    @15
    wa
    #
    @18
    @13
    @23
    @17
    @12
    vx
    cA
    @8
    cB
    cF
    fvimacnv
    ralbidv
    biimpa
    syl21anc
    @8
    cvv
    wcel
    #
    @10
    @13
    wb
    vy
    vex
    #
    vx
    @8
    cA
    @6
    cvv
    eliin
    #
    ax-mp
    #
    sylibr
    @2
    @10
    wa
    #
    @20
    @9
    @28
    @18
    @20
    @28
    @0
    @13
    @18
    @0
    @1
    @10
    simpll
    #
    @10
    @13
    @2
    @24
    @10
    @13
    wi
    @25
    @24
    @10
    @13
    @26
    biimpd
    ax-mp
    adantl
    @0
    @12
    @17
    vx
    cA
    @0
    @12
    @17
    @8
    cB
    cF
    fvimacnvi
    ex
    ralimdv
    sylc
    @19
    @20
    @18
    wb
    @21
    @22
    ax-mp
    sylibr
    @28
    @0
    @15
    @20
    @9
    wb
    @29
    @2
    @10
    @15
    @1
    @10
    @15
    wi
    @0
    @10
    @13
    @1
    @15
    @27
    @1
    @13
    @12
    vx
    cA
    wrex
    #
    @15
    @1
    @13
    @30
    wi
    @12
    vx
    cA
    r19.2zb
    biimpi
    @12
    @15
    vx
    cA
    @6
    @14
    @8
    cF
    cB
    cnvimass
    sseli
    rexlimivw
    syl6
    syl5bi
    adantl
    imp
    @8
    @4
    cF
    fvimacnv
    syl2anc
    mpbid
    impbida
    eqrdv
end
