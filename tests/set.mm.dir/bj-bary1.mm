include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cmin.mm"
include "cdiv.mm"
include "mulcld.mm"
include "addcomd.mm"
include "eqeq2d.mm"
include "biimpd.mm"
include "eqeq1d.mm"
include "necomd.mm"
include "bj-bary1lem1.mm"
include "syl2and.mm"
include "div2subd.mm"
include "sylibd.mm"
include "jcad.mm"
include "bj-bary1lem.mm"
include "wi.mm"
include "oveq1.mm"
include "oveqan12d.mm"
include "a1i.mm"
include "eqtr3.mm"
include "syl6an.mm"
include "oveq12.mm"
include "subcld.mm"
include "subne0d.mm"
include "divdird.mm"
include "npncand.mm"
include "diveq1bd.mm"
include "eqtr3d.mm"
include "syl5ib.mm"
include "impbid.mm"

theorem bj-bary1
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


  assert |- ( ph -> ( ( X = ( ( S x. A ) + ( T x. B ) ) /\ ( S + T ) = 1 ) <-> ( S = ( ( B - X ) / ( B - A ) ) /\ T = ( ( X - A ) / ( B - A ) ) ) ) )

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
    cS
    cB
    cX
    cmin
    co
    #
    cB
    cA
    cmin
    co
    #
    cdiv
    co
    #
    wceq
    #
    cT
    cX
    cA
    cmin
    co
    #
    @8
    cdiv
    co
    #
    wceq
    #
    wa
    #
    wph
    @6
    @10
    @13
    wph
    @6
    cS
    cX
    cB
    cmin
    co
    cA
    cB
    cmin
    co
    cdiv
    co
    #
    wceq
    #
    @10
    wph
    @3
    cX
    @1
    @0
    caddc
    co
    #
    wceq
    #
    @5
    cT
    cS
    caddc
    co
    #
    c1
    wceq
    #
    @16
    wph
    @3
    @18
    wph
    @2
    @17
    cX
    wph
    @0
    @1
    wph
    cS
    cA
    bj-bary1.s
    bj-bary1.a
    mulcld
    wph
    cT
    cB
    bj-bary1.t
    bj-bary1.b
    mulcld
    addcomd
    eqeq2d
    biimpd
    wph
    @5
    @20
    wph
    @4
    @19
    c1
    wph
    cS
    cT
    bj-bary1.s
    bj-bary1.t
    addcomd
    eqeq1d
    biimpd
    wph
    cB
    cA
    cT
    cS
    cX
    bj-bary1.b
    bj-bary1.a
    bj-bary1.x
    wph
    cA
    cB
    bj-bary1.neq
    necomd
    #
    bj-bary1.t
    bj-bary1.s
    bj-bary1lem1
    syl2and
    wph
    @15
    @9
    cS
    wph
    cX
    cB
    cA
    cB
    bj-bary1.x
    bj-bary1.b
    bj-bary1.a
    bj-bary1.b
    bj-bary1.neq
    div2subd
    eqeq2d
    sylibd
    wph
    cA
    cB
    cS
    cT
    cX
    bj-bary1.a
    bj-bary1.b
    bj-bary1.x
    bj-bary1.neq
    bj-bary1.s
    bj-bary1.t
    bj-bary1lem1
    jcad
    wph
    @14
    @3
    @5
    wph
    cX
    @9
    cA
    cmul
    co
    #
    @12
    cB
    cmul
    co
    #
    caddc
    co
    #
    wceq
    @14
    @2
    @24
    wceq
    #
    @3
    wph
    cA
    cB
    cX
    bj-bary1.a
    bj-bary1.b
    bj-bary1.x
    bj-bary1.neq
    bj-bary1lem
    @14
    @25
    wi
    wph
    @10
    @13
    @0
    @22
    @1
    @23
    caddc
    cS
    @9
    cA
    cmul
    oveq1
    cT
    @12
    cB
    cmul
    oveq1
    oveqan12d
    a1i
    cX
    @2
    @24
    eqtr3
    syl6an
    @14
    @4
    @9
    @12
    caddc
    co
    #
    wceq
    wph
    @5
    cS
    @9
    cT
    @12
    caddc
    oveq12
    wph
    @26
    c1
    @4
    wph
    @7
    @11
    caddc
    co
    #
    @8
    cdiv
    co
    @26
    c1
    wph
    @7
    @11
    @8
    wph
    cB
    cX
    bj-bary1.b
    bj-bary1.x
    subcld
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
    subcld
    #
    wph
    cB
    cA
    bj-bary1.b
    bj-bary1.a
    @21
    subne0d
    #
    divdird
    wph
    @27
    @8
    @28
    @29
    wph
    cB
    cX
    cA
    bj-bary1.b
    bj-bary1.x
    bj-bary1.a
    npncand
    diveq1bd
    eqtr3d
    eqeq2d
    syl5ib
    jcad
    impbid
end
