include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cmin.mm"
include "cdiv.mm"
include "wi.mm"
include "pncand.mm"
include "oveq1.mm"
include "pm5.31.mm"
include "sylancl.mm"
include "eqtr2.mm"
include "eqcomd.mm"
include "syl6.mm"
include "oveq1d.mm"
include "eqtr.mm"
include "sylan2.mm"
include "1cnd.mm"
include "subdird.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "sylan2d.mm"
include "mulcld.mm"
include "subadd23d.mm"
include "subdid.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "sylibd.mm"
include "subcld.mm"
include "pncan2d.mm"
include "syl5ib.mm"
include "eqcom.mm"
include "mulcomd.mm"
include "eqeq1d.mm"
include "necomd.mm"
include "subne0d.mm"
include "bj-rdiv.mm"
include "biimpd.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "3syld.mm"

theorem bj-bary1lem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cX: class X
  assume bj-bary1.a: |- ( ph -> A e. CC )
  assume bj-bary1.b: |- ( ph -> B e. CC )
  assume bj-bary1.x: |- ( ph -> X e. CC )
  assume bj-bary1.neq: |- ( ph -> A =/= B )
  assume bj-bary1.s: |- ( ph -> S e. CC )
  assume bj-bary1.t: |- ( ph -> T e. CC )


  assert |- ( ph -> ( ( X = ( ( S x. A ) + ( T x. B ) ) /\ ( S + T ) = 1 ) -> T = ( ( X - A ) / ( B - A ) ) ) )

  proof
    wph
    cX
    cS
    cA
    cmul
    co
    #
    cT
    cB
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    cS
    cT
    caddc
    co
    #
    c1
    wceq
    #
    wa
    #
    cX
    cA
    cT
    cB
    cA
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    cX
    cA
    cmin
    co
    #
    @8
    wceq
    #
    cT
    @11
    @7
    cdiv
    co
    wceq
    #
    wph
    @6
    cX
    cA
    cT
    cA
    cmul
    co
    #
    cmin
    co
    #
    @1
    caddc
    co
    #
    wceq
    #
    @10
    wph
    @5
    cS
    c1
    cT
    cmin
    co
    #
    wceq
    #
    @3
    @17
    wph
    @5
    @4
    cT
    cmin
    co
    #
    @18
    wceq
    #
    @20
    cS
    wceq
    #
    wa
    #
    @19
    wph
    @22
    @5
    @21
    wi
    @5
    @23
    wi
    wph
    cS
    cT
    bj-bary1.s
    bj-bary1.t
    pncand
    @4
    c1
    cT
    cmin
    oveq1
    @5
    @21
    @22
    pm5.31
    sylancl
    @23
    @18
    cS
    @20
    @18
    cS
    eqtr2
    eqcomd
    syl6
    wph
    @3
    @19
    wa
    #
    @17
    @24
    wph
    cX
    @18
    cA
    cmul
    co
    #
    @1
    caddc
    co
    #
    @16
    @19
    @3
    @2
    @26
    wceq
    cX
    @26
    wceq
    @19
    @0
    @25
    @1
    caddc
    cS
    @18
    cA
    cmul
    oveq1
    oveq1d
    cX
    @2
    @26
    eqtr
    sylan2
    wph
    @25
    @15
    @1
    caddc
    wph
    @25
    c1
    cA
    cmul
    co
    #
    @14
    cmin
    co
    @15
    wph
    c1
    cT
    cA
    wph
    1cnd
    bj-bary1.t
    bj-bary1.a
    subdird
    wph
    @27
    cA
    @14
    cmin
    wph
    cA
    bj-bary1.a
    mulid2d
    oveq1d
    eqtrd
    oveq1d
    sylan9eqr
    ex
    sylan2d
    wph
    @16
    @9
    cX
    wph
    @16
    cA
    @1
    @14
    cmin
    co
    #
    caddc
    co
    @9
    wph
    cA
    @14
    @1
    bj-bary1.a
    wph
    cT
    cA
    bj-bary1.t
    bj-bary1.a
    mulcld
    wph
    cT
    cB
    bj-bary1.t
    bj-bary1.b
    mulcld
    subadd23d
    wph
    @28
    @8
    cA
    caddc
    wph
    @8
    @28
    wph
    cT
    cB
    cA
    bj-bary1.t
    bj-bary1.b
    bj-bary1.a
    subdid
    eqcomd
    oveq2d
    eqtrd
    eqeq2d
    sylibd
    @10
    @11
    @9
    cA
    cmin
    co
    #
    wceq
    wph
    @12
    cX
    @9
    cA
    cmin
    oveq1
    wph
    @29
    @8
    @11
    wph
    cA
    @8
    bj-bary1.a
    wph
    cT
    @7
    bj-bary1.t
    wph
    cB
    cA
    bj-bary1.b
    bj-bary1.a
    subcld
    #
    mulcld
    pncan2d
    eqeq2d
    syl5ib
    @12
    @8
    @11
    wceq
    #
    wph
    @13
    @11
    @8
    eqcom
    wph
    @31
    @7
    cT
    cmul
    co
    #
    @11
    wceq
    #
    @13
    wph
    @8
    @32
    @11
    wph
    cT
    @7
    bj-bary1.t
    @30
    mulcomd
    eqeq1d
    wph
    @33
    @13
    wph
    @7
    cT
    @11
    @30
    bj-bary1.t
    wph
    cX
    cA
    bj-bary1.x
    bj-bary1.a
    subcld
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
    bj-rdiv
    biimpd
    sylbid
    syl5bi
    3syld
end
