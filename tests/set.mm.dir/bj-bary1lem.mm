include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "cdiv.mm"
include "caddc.mm"
include "cc0.mm"
include "mulcld.mm"
include "subcld.mm"
include "addsub12d.mm"
include "sub32d.mm"
include "bj-subcom.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "0cnd.mm"
include "addsubassd.mm"
include "addid1d.mm"
include "3eqtr2d.mm"
include "subdird.mm"
include "oveq12d.mm"
include "subdid.mm"
include "3eqtr4rd.mm"
include "necomd.mm"
include "subne0d.mm"
include "divdird.mm"
include "divcan4d.mm"
include "div23d.mm"
include "3eqtr3d.mm"

theorem bj-bary1lem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cX: class X
  assume bj-bary1.a: |- ( ph -> A e. CC )
  assume bj-bary1.b: |- ( ph -> B e. CC )
  assume bj-bary1.x: |- ( ph -> X e. CC )
  assume bj-bary1.neq: |- ( ph -> A =/= B )


  assert |- ( ph -> X = ( ( ( ( B - X ) / ( B - A ) ) x. A ) + ( ( ( X - A ) / ( B - A ) ) x. B ) ) )

  proof
    wph
    cX
    cB
    cA
    cmin
    co
    #
    cmul
    co
    #
    @0
    cdiv
    co
    #
    cB
    cX
    cmin
    co
    #
    cA
    cmul
    co
    #
    @0
    cdiv
    co
    #
    cX
    cA
    cmin
    co
    #
    cB
    cmul
    co
    #
    @0
    cdiv
    co
    #
    caddc
    co
    #
    cX
    @3
    @0
    cdiv
    co
    cA
    cmul
    co
    #
    @6
    @0
    cdiv
    co
    cB
    cmul
    co
    #
    caddc
    co
    wph
    @2
    @4
    @7
    caddc
    co
    #
    @0
    cdiv
    co
    @9
    wph
    @1
    @12
    @0
    cdiv
    wph
    cB
    cA
    cmul
    co
    #
    cX
    cA
    cmul
    co
    #
    cmin
    co
    #
    cX
    cB
    cmul
    co
    #
    cA
    cB
    cmul
    co
    #
    cmin
    co
    #
    caddc
    co
    #
    @16
    @14
    cmin
    co
    #
    @12
    @1
    wph
    @19
    @16
    cc0
    @14
    cmin
    co
    #
    caddc
    co
    #
    @16
    cc0
    caddc
    co
    #
    @14
    cmin
    co
    @20
    wph
    @19
    @16
    @15
    @17
    cmin
    co
    #
    caddc
    co
    @22
    wph
    @15
    @16
    @17
    wph
    @13
    @14
    wph
    cB
    cA
    bj-bary1.b
    bj-bary1.a
    mulcld
    #
    wph
    cX
    cA
    bj-bary1.x
    bj-bary1.a
    mulcld
    #
    subcld
    wph
    cX
    cB
    bj-bary1.x
    bj-bary1.b
    mulcld
    #
    wph
    cA
    cB
    bj-bary1.a
    bj-bary1.b
    mulcld
    #
    addsub12d
    wph
    @24
    @21
    @16
    caddc
    wph
    @24
    @13
    @17
    cmin
    co
    #
    @14
    cmin
    co
    @21
    wph
    @13
    @14
    @17
    @25
    @26
    @28
    sub32d
    wph
    @29
    cc0
    @14
    cmin
    wph
    cB
    cA
    bj-bary1.b
    bj-bary1.a
    bj-subcom
    oveq1d
    eqtrd
    oveq2d
    eqtrd
    wph
    @16
    cc0
    @14
    @27
    wph
    0cnd
    @26
    addsubassd
    wph
    @23
    @16
    @14
    cmin
    wph
    @16
    @27
    addid1d
    oveq1d
    3eqtr2d
    wph
    @4
    @15
    @7
    @18
    caddc
    wph
    cB
    cX
    cA
    bj-bary1.b
    bj-bary1.x
    bj-bary1.a
    subdird
    wph
    cX
    cA
    cB
    bj-bary1.x
    bj-bary1.a
    bj-bary1.b
    subdird
    oveq12d
    wph
    cX
    cB
    cA
    bj-bary1.x
    bj-bary1.b
    bj-bary1.a
    subdid
    3eqtr4rd
    oveq1d
    wph
    @4
    @7
    @0
    wph
    @3
    cA
    wph
    cB
    cX
    bj-bary1.b
    bj-bary1.x
    subcld
    #
    bj-bary1.a
    mulcld
    wph
    @6
    cB
    wph
    cX
    cA
    bj-bary1.x
    bj-bary1.a
    subcld
    #
    bj-bary1.b
    mulcld
    wph
    cB
    cA
    bj-bary1.b
    bj-bary1.a
    subcld
    #
    wph
    cB
    cA
    bj-bary1.b
    bj-bary1.a
    wph
    cA
    cB
    bj-bary1.neq
    necomd
    subne0d
    #
    divdird
    eqtrd
    wph
    cX
    @0
    bj-bary1.x
    @32
    @33
    divcan4d
    wph
    @5
    @10
    @8
    @11
    caddc
    wph
    @3
    cA
    @0
    @30
    bj-bary1.a
    @32
    @33
    div23d
    wph
    @6
    cB
    @0
    @31
    bj-bary1.b
    @32
    @33
    div23d
    oveq12d
    3eqtr3d
end
