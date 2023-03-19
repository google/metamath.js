include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "c0.mm"
include "csuc.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "cz.mm"
include "wcel.mm"
include "cc.mm"
include "zcn.mm"
include "ax-mp.mm"
include "pncan3i.mm"
include "om2uz0i.mm"
include "oveq1i.mm"
include "3eqtr4ri.mm"
include "com.mm"
include "c1.mm"
include "oveq1.mm"
include "om2uzsuci.mm"
include "cuz.mm"
include "om2uzuzi.mm"
include "eluzelz.mm"
include "syl.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "subcli.mm"
include "add32.mm"
include "mp3an23.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "finds.mm"

theorem uzrdgxfr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cG: class G
  let cH: class H
  let cN: class N
  let vk: setvar k
  let vy: setvar y
  assume uzrdgxfr.1: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , A ) |` _om )
  assume uzrdgxfr.2: |- H = ( rec ( ( x e. _V |-> ( x + 1 ) ) , B ) |` _om )
  assume uzrdgxfr.3: |- A e. ZZ
  assume uzrdgxfr.4: |- B e. ZZ

  disjoint A x
  disjoint B x
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A y
  disjoint B k
  disjoint B y
  disjoint G k
  disjoint G y
  disjoint H k
  disjoint H y
  disjoint N y
  assert |- ( N e. _om -> ( G ` N ) = ( ( H ` N ) + ( A - B ) ) )

  proof
    vy
    cv
    #
    cG
    cfv
    #
    @0
    cH
    cfv
    #
    cA
    cB
    cmin
    co
    #
    caddc
    co
    #
    wceq
    c0
    cG
    cfv
    #
    c0
    cH
    cfv
    #
    @3
    caddc
    co
    #
    wceq
    vk
    cv
    #
    cG
    cfv
    #
    @8
    cH
    cfv
    #
    @3
    caddc
    co
    #
    wceq
    #
    @8
    csuc
    #
    cG
    cfv
    #
    @13
    cH
    cfv
    #
    @3
    caddc
    co
    #
    wceq
    #
    cN
    cG
    cfv
    #
    cN
    cH
    cfv
    #
    @3
    caddc
    co
    #
    wceq
    vy
    vk
    cN
    @0
    c0
    wceq
    #
    @1
    @5
    @4
    @7
    @0
    c0
    cG
    fveq2
    @21
    @2
    @6
    @3
    caddc
    @0
    c0
    cH
    fveq2
    oveq1d
    eqeq12d
    @0
    @8
    wceq
    #
    @1
    @9
    @4
    @11
    @0
    @8
    cG
    fveq2
    @22
    @2
    @10
    @3
    caddc
    @0
    @8
    cH
    fveq2
    oveq1d
    eqeq12d
    @0
    @13
    wceq
    #
    @1
    @14
    @4
    @16
    @0
    @13
    cG
    fveq2
    @23
    @2
    @15
    @3
    caddc
    @0
    @13
    cH
    fveq2
    oveq1d
    eqeq12d
    @0
    cN
    wceq
    #
    @1
    @18
    @4
    @20
    @0
    cN
    cG
    fveq2
    @24
    @2
    @19
    @3
    caddc
    @0
    cN
    cH
    fveq2
    oveq1d
    eqeq12d
    cB
    @3
    caddc
    co
    cA
    @7
    @5
    cB
    cA
    cB
    cz
    wcel
    cB
    cc
    wcel
    uzrdgxfr.4
    cB
    zcn
    ax-mp
    #
    cA
    cz
    wcel
    cA
    cc
    wcel
    uzrdgxfr.3
    cA
    zcn
    ax-mp
    #
    pncan3i
    @6
    cB
    @3
    caddc
    vx
    cB
    cH
    uzrdgxfr.4
    uzrdgxfr.2
    om2uz0i
    oveq1i
    vx
    cA
    cG
    uzrdgxfr.3
    uzrdgxfr.1
    om2uz0i
    3eqtr4ri
    @12
    @17
    @8
    com
    wcel
    #
    @9
    c1
    caddc
    co
    #
    @11
    c1
    caddc
    co
    #
    wceq
    @9
    @11
    c1
    caddc
    oveq1
    @27
    @14
    @28
    @16
    @29
    vx
    @8
    cA
    cG
    uzrdgxfr.3
    uzrdgxfr.1
    om2uzsuci
    @27
    @16
    @10
    c1
    caddc
    co
    #
    @3
    caddc
    co
    #
    @29
    @27
    @15
    @30
    @3
    caddc
    vx
    @8
    cB
    cH
    uzrdgxfr.4
    uzrdgxfr.2
    om2uzsuci
    oveq1d
    @27
    @10
    cc
    wcel
    #
    @31
    @29
    wceq
    #
    @27
    @10
    @27
    @10
    cB
    cuz
    cfv
    wcel
    @10
    cz
    wcel
    vx
    @8
    cB
    cH
    uzrdgxfr.4
    uzrdgxfr.2
    om2uzuzi
    cB
    @10
    eluzelz
    syl
    zcnd
    @32
    c1
    cc
    wcel
    @3
    cc
    wcel
    @33
    ax-1cn
    cA
    cB
    @26
    @25
    subcli
    @10
    c1
    @3
    add32
    mp3an23
    syl
    eqtrd
    eqeq12d
    syl5ibr
    finds
end
