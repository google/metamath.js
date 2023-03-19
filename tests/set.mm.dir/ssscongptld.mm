include "cmin.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "cc.mm"
include "cr.mm"
include "negpitopissre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "subcld.mm"
include "subne0d.mm"
include "necomd.mm"
include "angcld.mm"
include "sseldi.mm"
include "coscld.mm"
include "abscld.mm"
include "recnd.mm"
include "mulcld.mm"
include "absne0d.mm"
include "mulne0d.mm"
include "abssubd.mm"
include "3eqtr4d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "c2.mm"
include "eqeltrd.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "cexp.mm"
include "caddc.mm"
include "sqcld.mm"
include "addcld.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "lawcos.mm"
include "syl32anc.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"
include "subcand.mm"
include "mulcanad.mm"

theorem ssscongptld
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  assume ssscongptld.angdef: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume ssscongptld.1: |- ( ph -> A e. CC )
  assume ssscongptld.2: |- ( ph -> B e. CC )
  assume ssscongptld.3: |- ( ph -> C e. CC )
  assume ssscongptld.4: |- ( ph -> D e. CC )
  assume ssscongptld.5: |- ( ph -> E e. CC )
  assume ssscongptld.6: |- ( ph -> G e. CC )
  assume ssscongptld.7: |- ( ph -> A =/= B )
  assume ssscongptld.8: |- ( ph -> B =/= C )
  assume ssscongptld.9: |- ( ph -> D =/= E )
  assume ssscongptld.10: |- ( ph -> E =/= G )
  assume ssscongptld.11: |- ( ph -> ( abs ` ( A - B ) ) = ( abs ` ( D - E ) ) )
  assume ssscongptld.12: |- ( ph -> ( abs ` ( B - C ) ) = ( abs ` ( E - G ) ) )
  assume ssscongptld.13: |- ( ph -> ( abs ` ( C - A ) ) = ( abs ` ( G - D ) ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint E x
  disjoint E y
  disjoint G x
  disjoint G y
  assert |- ( ph -> ( cos ` ( ( A - B ) F ( C - B ) ) ) = ( cos ` ( ( D - E ) F ( G - E ) ) ) )

  proof
    wph
    cA
    cB
    cmin
    co
    #
    cC
    cB
    cmin
    co
    #
    cF
    co
    #
    ccos
    cfv
    #
    cD
    cE
    cmin
    co
    #
    cG
    cE
    cmin
    co
    #
    cF
    co
    #
    ccos
    cfv
    #
    @4
    cabs
    cfv
    #
    @5
    cabs
    cfv
    #
    cmul
    co
    #
    wph
    @2
    wph
    cpi
    cneg
    cpi
    cioc
    co
    #
    cc
    @2
    @11
    cr
    cc
    negpitopissre
    ax-resscn
    sstri
    #
    wph
    vx
    vy
    cF
    @0
    @1
    ssscongptld.angdef
    wph
    cA
    cB
    ssscongptld.1
    ssscongptld.2
    subcld
    wph
    cA
    cB
    ssscongptld.1
    ssscongptld.2
    ssscongptld.7
    subne0d
    wph
    cC
    cB
    ssscongptld.3
    ssscongptld.2
    subcld
    wph
    cC
    cB
    ssscongptld.3
    ssscongptld.2
    wph
    cB
    cC
    ssscongptld.8
    necomd
    #
    subne0d
    angcld
    sseldi
    coscld
    #
    wph
    @6
    wph
    @11
    cc
    @6
    @12
    wph
    vx
    vy
    cF
    @4
    @5
    ssscongptld.angdef
    wph
    cD
    cE
    ssscongptld.4
    ssscongptld.5
    subcld
    #
    wph
    cD
    cE
    ssscongptld.4
    ssscongptld.5
    ssscongptld.9
    subne0d
    #
    wph
    cG
    cE
    ssscongptld.6
    ssscongptld.5
    subcld
    #
    wph
    cG
    cE
    ssscongptld.6
    ssscongptld.5
    wph
    cE
    cG
    ssscongptld.10
    necomd
    #
    subne0d
    #
    angcld
    sseldi
    coscld
    #
    wph
    @8
    @9
    wph
    @8
    wph
    @4
    @15
    abscld
    recnd
    #
    wph
    @9
    wph
    @5
    @17
    abscld
    recnd
    #
    mulcld
    #
    wph
    @8
    @9
    @21
    @22
    wph
    @4
    @15
    @16
    absne0d
    wph
    @5
    @17
    @19
    absne0d
    mulne0d
    wph
    @0
    cabs
    cfv
    #
    @1
    cabs
    cfv
    #
    cmul
    co
    #
    @3
    cmul
    co
    #
    @10
    @3
    cmul
    co
    @10
    @7
    cmul
    co
    #
    wph
    @26
    @10
    @3
    cmul
    wph
    @24
    @8
    @25
    @9
    cmul
    ssscongptld.11
    wph
    cB
    cC
    cmin
    co
    cabs
    cfv
    cE
    cG
    cmin
    co
    cabs
    cfv
    @25
    @9
    ssscongptld.12
    wph
    cC
    cB
    ssscongptld.3
    ssscongptld.2
    abssubd
    wph
    cG
    cE
    ssscongptld.6
    ssscongptld.5
    abssubd
    3eqtr4d
    #
    oveq12d
    oveq1d
    wph
    @27
    @28
    c2
    wph
    @26
    @3
    wph
    @24
    @25
    wph
    @24
    @8
    cc
    ssscongptld.11
    @21
    eqeltrd
    wph
    @25
    @9
    cc
    @29
    @22
    eqeltrd
    mulcld
    @14
    mulcld
    #
    wph
    @10
    @7
    @23
    @20
    mulcld
    #
    wph
    2cnd
    #
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    wph
    @8
    c2
    cexp
    co
    #
    @9
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    @27
    cmul
    co
    #
    c2
    @28
    cmul
    co
    #
    wph
    @33
    @34
    wph
    @8
    @21
    sqcld
    wph
    @9
    @22
    sqcld
    addcld
    wph
    c2
    @27
    @32
    @30
    mulcld
    wph
    c2
    @28
    @32
    @31
    mulcld
    wph
    @24
    c2
    cexp
    co
    #
    @25
    c2
    cexp
    co
    #
    caddc
    co
    #
    @36
    cmin
    co
    #
    @35
    @36
    cmin
    co
    @35
    @37
    cmin
    co
    #
    wph
    @40
    @35
    @36
    cmin
    wph
    @38
    @33
    @39
    @34
    caddc
    wph
    @24
    @8
    c2
    cexp
    ssscongptld.11
    oveq1d
    wph
    @25
    @9
    c2
    cexp
    @29
    oveq1d
    oveq12d
    oveq1d
    wph
    cC
    cA
    cmin
    co
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cG
    cD
    cmin
    co
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    @41
    @42
    wph
    @43
    @45
    c2
    cexp
    ssscongptld.13
    oveq1d
    wph
    cC
    cc
    wcel
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cB
    wne
    cA
    cB
    wne
    @44
    @41
    wceq
    ssscongptld.3
    ssscongptld.1
    ssscongptld.2
    @13
    ssscongptld.7
    vx
    vy
    cC
    cA
    cB
    cF
    @2
    @24
    @25
    @43
    ssscongptld.angdef
    @24
    eqid
    @25
    eqid
    @43
    eqid
    @2
    eqid
    lawcos
    syl32anc
    wph
    cG
    cc
    wcel
    cD
    cc
    wcel
    cE
    cc
    wcel
    cG
    cE
    wne
    cD
    cE
    wne
    @46
    @42
    wceq
    ssscongptld.6
    ssscongptld.4
    ssscongptld.5
    @18
    ssscongptld.9
    vx
    vy
    cG
    cD
    cE
    cF
    @6
    @8
    @9
    @45
    ssscongptld.angdef
    @8
    eqid
    @9
    eqid
    @45
    eqid
    @6
    eqid
    lawcos
    syl32anc
    3eqtr3d
    eqtr3d
    subcand
    mulcanad
    eqtr3d
    mulcanad
end
