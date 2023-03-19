include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cdv.mm"
include "c1.mm"
include "cmul.mm"
include "c2.mm"
include "cexp.mm"
include "cneg.mm"
include "caddc.mm"
include "cmin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "eldifad.mm"
include "wne.mm"
include "cdif.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simprd.mm"
include "divrecd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "reccld.mm"
include "1cnd.mm"
include "mulcld.mm"
include "sqcld.mm"
include "wceq.mm"
include "neneqd.mm"
include "wb.mm"
include "sqeq0.mm"
include "syl.mm"
include "mtbird.mm"
include "neqned.mm"
include "divcld.mm"
include "negcld.mm"
include "dvrecg.mm"
include "dvmptmul.mm"
include "dvmptcl.mm"
include "negsubd.mm"
include "div12d.mm"
include "mulid2d.mm"
include "sqvald.mm"
include "divcan5rd.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "negeqd.mm"
include "mulneg1d.mm"
include "div23d.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "divsubdird.mm"
include "3eqtr4d.mm"

theorem dvmptdiv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cV: class V
  let cX: class X
  assume dvmptdiv.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptdiv.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptdiv.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptdiv.da: |- ( ph -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )
  assume dvmptdiv.c: |- ( ( ph /\ x e. X ) -> C e. ( CC \ { 0 } ) )
  assume dvmptdiv.d: |- ( ( ph /\ x e. X ) -> D e. CC )
  assume dvmptdiv.dc: |- ( ph -> ( S _D ( x e. X |-> C ) ) = ( x e. X |-> D ) )

  disjoint S x
  disjoint V x
  disjoint X x
  disjoint ph x
  assert |- ( ph -> ( S _D ( x e. X |-> ( A / C ) ) ) = ( x e. X |-> ( ( ( B x. C ) - ( D x. A ) ) / ( C ^ 2 ) ) ) )

  proof
    wph
    cS
    vx
    cX
    cA
    cC
    cdiv
    co
    #
    cmpt
    #
    cdv
    co
    cS
    vx
    cX
    cA
    c1
    cC
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cX
    cB
    @2
    cmul
    co
    #
    c1
    cD
    cmul
    co
    #
    cC
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cneg
    #
    cA
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    vx
    cX
    cB
    cC
    cmul
    co
    #
    cD
    cA
    cmul
    co
    #
    cmin
    co
    @7
    cdiv
    co
    #
    cmpt
    wph
    @1
    @4
    cS
    cdv
    wph
    vx
    cX
    @0
    @3
    wph
    vx
    cv
    cX
    wcel
    wa
    #
    cA
    cC
    dvmptdiv.a
    @15
    cC
    cc
    cc0
    csn
    #
    dvmptdiv.c
    eldifad
    #
    @15
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    @15
    cC
    cc
    @16
    cdif
    wcel
    @18
    @19
    wa
    dvmptdiv.c
    cC
    cc
    cc0
    eldifsn
    sylib
    simprd
    #
    divrecd
    mpteq2dva
    oveq2d
    wph
    vx
    cA
    cB
    @2
    @9
    cS
    cV
    cc
    cX
    dvmptdiv.s
    dvmptdiv.a
    dvmptdiv.b
    dvmptdiv.da
    @15
    cC
    @17
    @20
    reccld
    @15
    @8
    @15
    @6
    @7
    @15
    c1
    cD
    @15
    1cnd
    #
    dvmptdiv.d
    mulcld
    @15
    cC
    @17
    sqcld
    #
    @15
    @7
    cc0
    @15
    @7
    cc0
    wceq
    #
    cC
    cc0
    wceq
    #
    @15
    cC
    cc0
    @20
    neneqd
    @15
    @18
    @23
    @24
    wb
    @17
    cC
    sqeq0
    syl
    mtbird
    neqned
    #
    divcld
    negcld
    wph
    vx
    c1
    cC
    cD
    cS
    cc
    cX
    dvmptdiv.s
    wph
    1cnd
    dvmptdiv.c
    dvmptdiv.d
    dvmptdiv.dc
    dvrecg
    dvmptmul
    wph
    vx
    cX
    @11
    @14
    @15
    @12
    @7
    cdiv
    co
    #
    @13
    @7
    cdiv
    co
    #
    cneg
    #
    caddc
    co
    @26
    @27
    cmin
    co
    @11
    @14
    @15
    @26
    @27
    @15
    @12
    @7
    @15
    cB
    cC
    wph
    vx
    cA
    cB
    cS
    cV
    cX
    dvmptdiv.s
    dvmptdiv.a
    dvmptdiv.b
    dvmptdiv.da
    dvmptcl
    #
    @17
    mulcld
    #
    @22
    @25
    divcld
    @15
    @13
    @7
    @15
    cD
    cA
    dvmptdiv.d
    dvmptdiv.a
    mulcld
    #
    @22
    @25
    divcld
    negsubd
    @15
    @5
    @26
    @10
    @28
    caddc
    @15
    @5
    c1
    cB
    cC
    cdiv
    co
    #
    cmul
    co
    @32
    @26
    @15
    cB
    c1
    cC
    @29
    @21
    @17
    @20
    div12d
    @15
    @32
    @15
    cB
    cC
    @29
    @17
    @20
    divcld
    mulid2d
    @15
    @26
    @12
    cC
    cC
    cmul
    co
    #
    cdiv
    co
    @32
    @15
    @7
    @33
    @12
    cdiv
    @15
    cC
    @17
    sqvald
    oveq2d
    @15
    cB
    cC
    cC
    @29
    @17
    @17
    @20
    @20
    divcan5rd
    eqtr2d
    3eqtrd
    @15
    @10
    cD
    @7
    cdiv
    co
    #
    cneg
    #
    cA
    cmul
    co
    @34
    cA
    cmul
    co
    #
    cneg
    @28
    @15
    @9
    @35
    cA
    cmul
    @15
    @8
    @34
    @15
    @6
    cD
    @7
    cdiv
    @15
    cD
    dvmptdiv.d
    mulid2d
    oveq1d
    negeqd
    oveq1d
    @15
    @34
    cA
    @15
    cD
    @7
    dvmptdiv.d
    @22
    @25
    divcld
    dvmptdiv.a
    mulneg1d
    @15
    @36
    @27
    @15
    @27
    @36
    @15
    cD
    cA
    @7
    dvmptdiv.d
    dvmptdiv.a
    @22
    @25
    div23d
    eqcomd
    negeqd
    3eqtrd
    oveq12d
    @15
    @12
    @13
    @7
    @30
    @31
    @22
    @25
    divsubdird
    3eqtr4d
    mpteq2dva
    3eqtrd
end
