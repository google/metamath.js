include "cc.mm"
include "wcel.mm"
include "c3.mm"
include "c8.mm"
include "cdiv.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "cmin.mm"
include "3cn.mm"
include "8cn.mm"
include "8nn.mm"
include "nnne0i.mm"
include "divcli.mm"
include "sqcld.mm"
include "mulcl.mm"
include "sylancr.mm"
include "subcld.mm"
include "eqeltrd.mm"
include "caddc.mm"
include "mulcld.mm"
include "halfcld.mm"
include "cn0.mm"
include "3nn0.mm"
include "expcl.mm"
include "sylancl.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "divcld.mm"
include "addcld.mm"
include "c4.mm"
include "c1.mm"
include "c6.mm"
include "cdc.mm"
include "c5.mm"
include "4cn.mm"
include "4ne0.mm"
include "1nn0.mm"
include "6nn.mm"
include "decnncl.mm"
include "nncni.mm"
include "2nn0.mm"
include "5nn0.mm"
include "deccl.mm"
include "4nn0.mm"
include "3jca.mm"

theorem quart1cl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  assume quart1.a: |- ( ph -> A e. CC )
  assume quart1.b: |- ( ph -> B e. CC )
  assume quart1.c: |- ( ph -> C e. CC )
  assume quart1.d: |- ( ph -> D e. CC )
  assume quart1.p: |- ( ph -> P = ( B - ( ( 3 / 8 ) x. ( A ^ 2 ) ) ) )
  assume quart1.q: |- ( ph -> Q = ( ( C - ( ( A x. B ) / 2 ) ) + ( ( A ^ 3 ) / 8 ) ) )
  assume quart1.r: |- ( ph -> R = ( ( D - ( ( C x. A ) / 4 ) ) + ( ( ( ( A ^ 2 ) x. B ) / ; 1 6 ) - ( ( 3 / ; ; 2 5 6 ) x. ( A ^ 4 ) ) ) ) )


  assert |- ( ph -> ( P e. CC /\ Q e. CC /\ R e. CC ) )

  proof
    wph
    cP
    cc
    wcel
    cQ
    cc
    wcel
    cR
    cc
    wcel
    wph
    cP
    cB
    c3
    c8
    cdiv
    co
    #
    cA
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    cc
    quart1.p
    wph
    cB
    @2
    quart1.b
    wph
    @0
    cc
    wcel
    @1
    cc
    wcel
    @2
    cc
    wcel
    c3
    c8
    3cn
    8cn
    c8
    8nn
    nnne0i
    #
    divcli
    wph
    cA
    quart1.a
    sqcld
    #
    @0
    @1
    mulcl
    sylancr
    subcld
    eqeltrd
    wph
    cQ
    cC
    cA
    cB
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cmin
    co
    #
    cA
    c3
    cexp
    co
    #
    c8
    cdiv
    co
    #
    caddc
    co
    cc
    quart1.q
    wph
    @7
    @9
    wph
    cC
    @6
    quart1.c
    wph
    @5
    wph
    cA
    cB
    quart1.a
    quart1.b
    mulcld
    halfcld
    subcld
    wph
    @8
    c8
    wph
    cA
    cc
    wcel
    #
    c3
    cn0
    wcel
    @8
    cc
    wcel
    quart1.a
    3nn0
    cA
    c3
    expcl
    sylancl
    c8
    cc
    wcel
    wph
    8cn
    a1i
    c8
    cc0
    wne
    wph
    @3
    a1i
    divcld
    addcld
    eqeltrd
    wph
    cR
    cD
    cC
    cA
    cmul
    co
    #
    c4
    cdiv
    co
    #
    cmin
    co
    #
    @1
    cB
    cmul
    co
    #
    c1
    c6
    cdc
    #
    cdiv
    co
    #
    c3
    c2
    c5
    cdc
    #
    c6
    cdc
    #
    cdiv
    co
    #
    cA
    c4
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    caddc
    co
    cc
    quart1.r
    wph
    @13
    @22
    wph
    cD
    @12
    quart1.d
    wph
    @11
    c4
    wph
    cC
    cA
    quart1.c
    quart1.a
    mulcld
    c4
    cc
    wcel
    wph
    4cn
    a1i
    c4
    cc0
    wne
    wph
    4ne0
    a1i
    divcld
    subcld
    wph
    @16
    @21
    wph
    @14
    @15
    wph
    @1
    cB
    @4
    quart1.b
    mulcld
    @15
    cc
    wcel
    wph
    @15
    c1
    c6
    1nn0
    6nn
    decnncl
    #
    nncni
    a1i
    @15
    cc0
    wne
    wph
    @15
    @23
    nnne0i
    a1i
    divcld
    wph
    @19
    cc
    wcel
    @20
    cc
    wcel
    #
    @21
    cc
    wcel
    c3
    @18
    3cn
    @18
    @17
    c6
    c2
    c5
    2nn0
    5nn0
    deccl
    6nn
    decnncl
    #
    nncni
    @18
    @25
    nnne0i
    divcli
    wph
    @10
    c4
    cn0
    wcel
    @24
    quart1.a
    4nn0
    cA
    c4
    expcl
    sylancl
    @19
    @20
    mulcl
    sylancr
    subcld
    addcld
    eqeltrd
    3jca
end
