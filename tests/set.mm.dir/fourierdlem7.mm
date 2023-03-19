include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "resubcld.mm"
include "syl5eqel.mm"
include "cc0.mm"
include "clt.mm"
include "posdifd.mm"
include "mpbid.mm"
include "syl6breqr.mm"
include "gt0ne0d.mm"
include "redivcld.mm"
include "elrpd.mm"
include "lesub2dd.mm"
include "lediv1dd.mm"
include "flwordi.mm"
include "syl3anc.mm"
include "flcld.mm"
include "zred.mm"
include "lemul1d.mm"
include "caddc.mm"
include "cv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "id.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "adantl.mm"
include "remulcld.mm"
include "readdcld.mm"
include "fvmptd.mm"
include "recnd.mm"
include "pncan2d.mm"
include "eqtrd.mm"
include "3brtr4d.mm"

theorem fourierdlem7
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let cE: class E
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume fourierdlem7.a: |- ( ph -> A e. RR )
  assume fourierdlem7.b: |- ( ph -> B e. RR )
  assume fourierdlem7.altb: |- ( ph -> A < B )
  assume fourierdlem7.t: |- T = ( B - A )
  assume fourierdlem7.e: |- E = ( x e. RR |-> ( x + ( ( |_ ` ( ( B - x ) / T ) ) x. T ) ) )
  assume fourierdlem7.x: |- ( ph -> X e. RR )
  assume fourierdlem7.y: |- ( ph -> Y e. RR )
  assume fourierdlem7.xlty: |- ( ph -> X <_ Y )

  disjoint B x
  disjoint T x
  disjoint X x
  disjoint Y x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( E ` Y ) - Y ) <_ ( ( E ` X ) - X ) )

  proof
    wph
    cB
    cY
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    cB
    cX
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    cY
    cE
    cfv
    #
    cY
    cmin
    co
    #
    cX
    cE
    cfv
    #
    cX
    cmin
    co
    #
    cle
    wph
    @2
    @6
    cle
    wbr
    #
    @3
    @7
    cle
    wbr
    wph
    @1
    cr
    wcel
    @5
    cr
    wcel
    @1
    @5
    cle
    wbr
    @12
    wph
    @0
    cT
    wph
    cB
    cY
    fourierdlem7.b
    fourierdlem7.y
    resubcld
    #
    wph
    cT
    cB
    cA
    cmin
    co
    #
    cr
    fourierdlem7.t
    wph
    cB
    cA
    fourierdlem7.b
    fourierdlem7.a
    resubcld
    syl5eqel
    #
    wph
    cT
    wph
    cc0
    @14
    cT
    clt
    wph
    cA
    cB
    clt
    wbr
    cc0
    @14
    clt
    wbr
    fourierdlem7.altb
    wph
    cA
    cB
    fourierdlem7.a
    fourierdlem7.b
    posdifd
    mpbid
    fourierdlem7.t
    syl6breqr
    #
    gt0ne0d
    #
    redivcld
    #
    wph
    @4
    cT
    wph
    cB
    cX
    fourierdlem7.b
    fourierdlem7.x
    resubcld
    #
    @15
    @17
    redivcld
    #
    wph
    @0
    @4
    cT
    @13
    @19
    wph
    cT
    @15
    @16
    elrpd
    #
    wph
    cX
    cY
    cB
    fourierdlem7.x
    fourierdlem7.y
    fourierdlem7.b
    fourierdlem7.xlty
    lesub2dd
    lediv1dd
    @1
    @5
    flwordi
    syl3anc
    wph
    @2
    @6
    cT
    wph
    @2
    wph
    @1
    @18
    flcld
    zred
    #
    wph
    @6
    wph
    @5
    @20
    flcld
    zred
    #
    @21
    lemul1d
    mpbid
    wph
    @9
    cY
    @3
    caddc
    co
    #
    cY
    cmin
    co
    @3
    wph
    @8
    @24
    cY
    cmin
    wph
    vx
    cY
    vx
    cv
    #
    cB
    @25
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    @24
    cr
    cE
    cr
    cE
    vx
    cr
    @30
    cmpt
    wceq
    wph
    fourierdlem7.e
    a1i
    #
    @25
    cY
    wceq
    #
    @30
    @24
    wceq
    wph
    @32
    @25
    cY
    @29
    @3
    caddc
    @32
    id
    @32
    @28
    @2
    cT
    cmul
    @32
    @27
    @1
    cfl
    @32
    @26
    @0
    cT
    cdiv
    @25
    cY
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    adantl
    fourierdlem7.y
    wph
    cY
    @3
    fourierdlem7.y
    wph
    @2
    cT
    @22
    @15
    remulcld
    #
    readdcld
    fvmptd
    oveq1d
    wph
    cY
    @3
    wph
    cY
    fourierdlem7.y
    recnd
    wph
    @3
    @33
    recnd
    pncan2d
    eqtrd
    wph
    @11
    cX
    @7
    caddc
    co
    #
    cX
    cmin
    co
    @7
    wph
    @10
    @34
    cX
    cmin
    wph
    vx
    cX
    @30
    @34
    cr
    cE
    cr
    @31
    @25
    cX
    wceq
    #
    @30
    @34
    wceq
    wph
    @35
    @25
    cX
    @29
    @7
    caddc
    @35
    id
    @35
    @28
    @6
    cT
    cmul
    @35
    @27
    @5
    cfl
    @35
    @26
    @4
    cT
    cdiv
    @25
    cX
    cB
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    adantl
    fourierdlem7.x
    wph
    cX
    @7
    fourierdlem7.x
    wph
    @6
    cT
    @23
    @15
    remulcld
    #
    readdcld
    fvmptd
    oveq1d
    wph
    cX
    @7
    wph
    cX
    fourierdlem7.x
    recnd
    wph
    @7
    @36
    recnd
    pncan2d
    eqtrd
    3brtr4d
end
