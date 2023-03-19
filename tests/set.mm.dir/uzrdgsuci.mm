include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "ccnv.mm"
include "csuc.mm"
include "c2nd.mm"
include "wfun.mm"
include "cop.mm"
include "wceq.mm"
include "wfn.mm"
include "uzrdgfni.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "crn.mm"
include "peano2uz.mm"
include "uzrdglem.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "funopfv.mm"
include "mpsyl.mm"
include "com.mm"
include "wf1o.mm"
include "om2uzf1oi.mm"
include "f1ocnvdm.mm"
include "mpan.mm"
include "peano2.mm"
include "om2uzsuci.mm"
include "f1ocnvfv2.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "wi.mm"
include "f1ocnvfv.mm"
include "sylc.mm"
include "fveq2d.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt2.mm"
include "crdg.mm"
include "cres.mm"
include "frsuc.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "om2uzrdg.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "fvex.mm"
include "oveq1.mm"
include "opeq12d.mm"
include "oveq2.mm"
include "opeq2d.mm"
include "cbvmpt2v.mm"
include "opex.mm"
include "ovmpt2.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "ovex.mm"
include "op2nd.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem uzrdgsuci
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume om2uz.1: |- C e. ZZ
  assume om2uz.2: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , C ) |` _om )
  assume uzrdg.1: |- A e. _V
  assume uzrdg.2: |- R = ( rec ( ( x e. _V , y e. _V |-> <. ( x + 1 ) , ( x F y ) >. ) , <. C , A >. ) |` _om )
  assume uzrdg.3: |- S = ran R

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
  disjoint S v
  disjoint S w
  disjoint S z
  assert |- ( B e. ( ZZ>= ` C ) -> ( S ` ( B + 1 ) ) = ( B F ( S ` B ) ) )

  proof
    cB
    cC
    cuz
    cfv
    #
    wcel
    #
    cB
    c1
    caddc
    co
    #
    cS
    cfv
    #
    cB
    cG
    ccnv
    #
    cfv
    #
    csuc
    #
    cR
    cfv
    #
    c2nd
    cfv
    #
    @5
    cG
    cfv
    #
    @5
    cR
    cfv
    #
    c2nd
    cfv
    #
    cF
    co
    #
    cB
    cB
    cS
    cfv
    #
    cF
    co
    @1
    @3
    @2
    @4
    cfv
    #
    cR
    cfv
    #
    c2nd
    cfv
    #
    @8
    cS
    wfun
    #
    @1
    @2
    @16
    cop
    #
    cS
    wcel
    @3
    @16
    wceq
    cS
    @0
    wfn
    @17
    vx
    vy
    cA
    cC
    cR
    cS
    cF
    cG
    om2uz.1
    om2uz.2
    uzrdg.1
    uzrdg.2
    uzrdg.3
    uzrdgfni
    @0
    cS
    fnfun
    ax-mp
    #
    @1
    @18
    cR
    crn
    #
    cS
    @1
    @2
    @0
    wcel
    @18
    @20
    wcel
    cC
    cB
    peano2uz
    vx
    vy
    cA
    @2
    cC
    cR
    cF
    cG
    om2uz.1
    om2uz.2
    uzrdg.1
    uzrdg.2
    uzrdglem
    syl
    uzrdg.3
    syl6eleqr
    @2
    @16
    cS
    funopfv
    mpsyl
    @1
    @15
    @7
    c2nd
    @1
    @14
    @6
    cR
    @1
    @6
    com
    wcel
    #
    @6
    cG
    cfv
    #
    @2
    wceq
    #
    @14
    @6
    wceq
    #
    @1
    @5
    com
    wcel
    #
    @21
    com
    @0
    cG
    wf1o
    #
    @1
    @25
    vx
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzf1oi
    #
    com
    @0
    cB
    cG
    f1ocnvdm
    mpan
    #
    @5
    peano2
    syl
    @1
    @22
    @9
    c1
    caddc
    co
    #
    @2
    @1
    @25
    @22
    @29
    wceq
    @28
    vx
    @5
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzsuci
    syl
    @1
    @9
    cB
    c1
    caddc
    @26
    @1
    @9
    cB
    wceq
    @27
    com
    @0
    cB
    cG
    f1ocnvfv2
    mpan
    #
    oveq1d
    eqtrd
    @26
    @21
    @23
    @24
    wi
    @27
    com
    @0
    @6
    @2
    cG
    f1ocnvfv
    mpan
    sylc
    fveq2d
    fveq2d
    eqtrd
    @1
    @25
    @8
    @12
    wceq
    @28
    @25
    @8
    @29
    @12
    cop
    #
    c2nd
    cfv
    @12
    @25
    @7
    @31
    c2nd
    @25
    @7
    @9
    @11
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
    @32
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
    co
    #
    @31
    @25
    @7
    @10
    @37
    cfv
    #
    @38
    @25
    @6
    @37
    cC
    cA
    cop
    #
    crdg
    com
    cres
    #
    cfv
    @5
    @41
    cfv
    #
    @37
    cfv
    @7
    @39
    @40
    @5
    @37
    frsuc
    @6
    cR
    @41
    uzrdg.2
    fveq1i
    @10
    @42
    @37
    @5
    cR
    @41
    uzrdg.2
    fveq1i
    fveq2i
    3eqtr4g
    @25
    @39
    @9
    @11
    cop
    #
    @37
    cfv
    @38
    @25
    @10
    @43
    @37
    vx
    vy
    cA
    @5
    cC
    cR
    cF
    cG
    om2uz.1
    om2uz.2
    uzrdg.1
    uzrdg.2
    om2uzrdg
    fveq2d
    @9
    @11
    @37
    df-ov
    syl6eqr
    eqtrd
    @9
    cvv
    wcel
    @11
    cvv
    wcel
    @38
    @31
    wceq
    @5
    cG
    fvex
    @10
    c2nd
    fvex
    vz
    vw
    @9
    @11
    cvv
    cvv
    vz
    cv
    #
    c1
    caddc
    co
    #
    @44
    vw
    cv
    #
    cF
    co
    #
    cop
    #
    @31
    @37
    @29
    @9
    @46
    cF
    co
    #
    cop
    @44
    @9
    wceq
    @45
    @29
    @47
    @49
    @44
    @9
    c1
    caddc
    oveq1
    @44
    @9
    @46
    cF
    oveq1
    opeq12d
    @46
    @11
    wceq
    @49
    @12
    @29
    @46
    @11
    @9
    cF
    oveq2
    opeq2d
    vx
    vy
    vz
    vw
    cvv
    cvv
    @36
    @48
    @45
    @44
    @34
    cF
    co
    #
    cop
    @32
    @44
    wceq
    @33
    @45
    @35
    @50
    @32
    @44
    c1
    caddc
    oveq1
    @32
    @44
    @34
    cF
    oveq1
    opeq12d
    @34
    @46
    wceq
    @50
    @47
    @45
    @34
    @46
    @44
    cF
    oveq2
    opeq2d
    cbvmpt2v
    @29
    @12
    opex
    ovmpt2
    mp2an
    syl6eq
    fveq2d
    @29
    @12
    @9
    c1
    caddc
    ovex
    @9
    @11
    cF
    ovex
    op2nd
    syl6eq
    syl
    @1
    @9
    cB
    @11
    @13
    cF
    @30
    @1
    @13
    @11
    @17
    @1
    cB
    @11
    cop
    #
    cS
    wcel
    @13
    @11
    wceq
    @19
    @1
    @51
    @20
    cS
    vx
    vy
    cA
    cB
    cC
    cR
    cF
    cG
    om2uz.1
    om2uz.2
    uzrdg.1
    uzrdg.2
    uzrdglem
    uzrdg.3
    syl6eleqr
    cB
    @11
    cS
    funopfv
    mpsyl
    eqcomd
    oveq12d
    3eqtrd
end
