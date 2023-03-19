include "cv.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "c0.mm"
include "csuc.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "eqeq12d.mm"
include "cvv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt2.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "fveq1i.mm"
include "wcel.mm"
include "opex.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "om2uz0i.mm"
include "fveq2i.mm"
include "cz.mm"
include "elexi.mm"
include "op2nd.mm"
include "opeq12i.mm"
include "eqtr4i.mm"
include "wa.mm"
include "frsuc.mm"
include "3eqtr4g.mm"
include "df-ov.mm"
include "fvex.mm"
include "oveq1.mm"
include "oveq2.mm"
include "opeq2d.mm"
include "cbvmpt2v.mm"
include "ovmpt2.mm"
include "mp2an.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "om2uzsuci.mm"
include "adantr.mm"
include "ovex.mm"
include "eqtr4d.mm"
include "ex.mm"
include "finds.mm"

theorem om2uzrdg
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume om2uz.1: |- C e. ZZ
  assume om2uz.2: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , C ) |` _om )
  assume uzrdg.1: |- A e. _V
  assume uzrdg.2: |- R = ( rec ( ( x e. _V , y e. _V |-> <. ( x + 1 ) , ( x F y ) >. ) , <. C , A >. ) |` _om )

  disjoint A y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint G y
  disjoint F x
  disjoint F y
  disjoint y z
  disjoint A z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint C w
  disjoint x z
  disjoint C z
  disjoint G v
  disjoint G w
  disjoint G z
  disjoint F w
  disjoint F z
  disjoint R v
  disjoint R w
  disjoint R z
  assert |- ( B e. _om -> ( R ` B ) = <. ( G ` B ) , ( 2nd ` ( R ` B ) ) >. )

  proof
    vz
    cv
    #
    cR
    cfv
    #
    @0
    cG
    cfv
    #
    @1
    c2nd
    cfv
    #
    cop
    #
    wceq
    c0
    cR
    cfv
    #
    c0
    cG
    cfv
    #
    @5
    c2nd
    cfv
    #
    cop
    #
    wceq
    vv
    cv
    #
    cR
    cfv
    #
    @9
    cG
    cfv
    #
    @10
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    @9
    csuc
    #
    cR
    cfv
    #
    @15
    cG
    cfv
    #
    @16
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    cB
    cR
    cfv
    #
    cB
    cG
    cfv
    #
    @21
    c2nd
    cfv
    #
    cop
    #
    wceq
    vz
    vv
    cB
    @0
    c0
    wceq
    #
    @1
    @5
    @4
    @8
    @0
    c0
    cR
    fveq2
    #
    @25
    @2
    @6
    @3
    @7
    @0
    c0
    cG
    fveq2
    @25
    @1
    @5
    c2nd
    @26
    fveq2d
    opeq12d
    eqeq12d
    @0
    @9
    wceq
    #
    @1
    @10
    @4
    @13
    @0
    @9
    cR
    fveq2
    #
    @27
    @2
    @11
    @3
    @12
    @0
    @9
    cG
    fveq2
    @27
    @1
    @10
    c2nd
    @28
    fveq2d
    opeq12d
    eqeq12d
    @0
    @15
    wceq
    #
    @1
    @16
    @4
    @19
    @0
    @15
    cR
    fveq2
    #
    @29
    @2
    @17
    @3
    @18
    @0
    @15
    cG
    fveq2
    @29
    @1
    @16
    c2nd
    @30
    fveq2d
    opeq12d
    eqeq12d
    @0
    cB
    wceq
    #
    @1
    @21
    @4
    @24
    @0
    cB
    cR
    fveq2
    #
    @31
    @2
    @22
    @3
    @23
    @0
    cB
    cG
    fveq2
    @31
    @1
    @21
    c2nd
    @32
    fveq2d
    opeq12d
    eqeq12d
    @5
    cC
    cA
    cop
    #
    @8
    @5
    c0
    vx
    vy
    cvv
    cvv
    vx
    cv
    #
    c1
    caddc
    co
    #
    @34
    vy
    cv
    #
    cF
    co
    #
    cop
    #
    cmpt2
    #
    @33
    crdg
    com
    cres
    #
    cfv
    #
    @33
    c0
    cR
    @40
    uzrdg.2
    fveq1i
    @33
    cvv
    wcel
    @41
    @33
    wceq
    cC
    cA
    opex
    @33
    cvv
    @39
    fr0g
    ax-mp
    eqtri
    #
    @6
    cC
    @7
    cA
    vx
    cC
    cG
    om2uz.1
    om2uz.2
    om2uz0i
    @7
    @33
    c2nd
    cfv
    cA
    @5
    @33
    c2nd
    @42
    fveq2i
    cC
    cA
    cC
    cz
    om2uz.1
    elexi
    uzrdg.1
    op2nd
    eqtri
    opeq12i
    eqtr4i
    @9
    com
    wcel
    #
    @14
    @20
    @43
    @14
    wa
    #
    @16
    @11
    c1
    caddc
    co
    #
    @11
    @12
    cF
    co
    #
    cop
    #
    @19
    @43
    @14
    @16
    @10
    @39
    cfv
    #
    @47
    @43
    @15
    @40
    cfv
    @9
    @40
    cfv
    #
    @39
    cfv
    @16
    @48
    @33
    @9
    @39
    frsuc
    @15
    cR
    @40
    uzrdg.2
    fveq1i
    @10
    @49
    @39
    @9
    cR
    @40
    uzrdg.2
    fveq1i
    fveq2i
    3eqtr4g
    @14
    @48
    @13
    @39
    cfv
    #
    @47
    @10
    @13
    @39
    fveq2
    @11
    @12
    @39
    co
    #
    @50
    @47
    @11
    @12
    @39
    df-ov
    @11
    cvv
    wcel
    @12
    cvv
    wcel
    @51
    @47
    wceq
    @9
    cG
    fvex
    @10
    c2nd
    fvex
    vw
    vz
    @11
    @12
    cvv
    cvv
    vw
    cv
    #
    c1
    caddc
    co
    #
    @52
    @0
    cF
    co
    #
    cop
    #
    @47
    @39
    @45
    @11
    @0
    cF
    co
    #
    cop
    @52
    @11
    wceq
    @53
    @45
    @54
    @56
    @52
    @11
    c1
    caddc
    oveq1
    @52
    @11
    @0
    cF
    oveq1
    opeq12d
    @0
    @12
    wceq
    @56
    @46
    @45
    @0
    @12
    @11
    cF
    oveq2
    opeq2d
    vx
    vy
    vw
    vz
    cvv
    cvv
    @38
    @55
    @53
    @52
    @36
    cF
    co
    #
    cop
    @34
    @52
    wceq
    @35
    @53
    @37
    @57
    @34
    @52
    c1
    caddc
    oveq1
    @34
    @52
    @36
    cF
    oveq1
    opeq12d
    @36
    @0
    wceq
    @57
    @54
    @53
    @36
    @0
    @52
    cF
    oveq2
    opeq2d
    cbvmpt2v
    @45
    @46
    opex
    ovmpt2
    mp2an
    eqtr3i
    syl6eq
    sylan9eq
    #
    @44
    @17
    @45
    @18
    @46
    @43
    @17
    @45
    wceq
    @14
    vx
    @9
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzsuci
    adantr
    @44
    @18
    @47
    c2nd
    cfv
    @46
    @44
    @16
    @47
    c2nd
    @58
    fveq2d
    @45
    @46
    @11
    c1
    caddc
    ovex
    @11
    @12
    cF
    ovex
    op2nd
    syl6eq
    opeq12d
    eqtr4d
    ex
    finds
end
