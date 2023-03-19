include "cdiv.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cpi.mm"
include "c2.mm"
include "cneg.mm"
include "cpr.mm"
include "wcel.mm"
include "wn.mm"
include "wb.mm"
include "divne0d.mm"
include "neneqd.mm"
include "biorf.mm"
include "syl.mm"
include "angrteqvd.mm"
include "cmul.mm"
include "dmdcan2d.mm"
include "fveq2d.mm"
include "divcld.mm"
include "remul2d.mm"
include "eqtr3d.mm"
include "eqeq1d.mm"
include "recld.mm"
include "recnd.mm"
include "mul0ord.mm"
include "3bitrd.mm"
include "3bitr4d.mm"

theorem angrtmuld
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let cA: class A
  let cB: class B
  let cC: class C
  assume ang.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume angrtmuld.1: |- ( ph -> X e. CC )
  assume angrtmuld.2: |- ( ph -> Y e. CC )
  assume angrtmuld.3: |- ( ph -> Z e. CC )
  assume angrtmuld.4: |- ( ph -> X =/= 0 )
  assume angrtmuld.5: |- ( ph -> Y =/= 0 )
  assume angrtmuld.6: |- ( ph -> Z =/= 0 )
  assume angrtmuld.7: |- ( ph -> ( Z / Y ) e. RR )

  disjoint x y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ph -> ( ( X F Y ) e. { ( _pi / 2 ) , -u ( _pi / 2 ) } <-> ( X F Z ) e. { ( _pi / 2 ) , -u ( _pi / 2 ) } ) )

  proof
    wph
    cY
    cX
    cdiv
    co
    #
    cre
    cfv
    #
    cc0
    wceq
    #
    cZ
    cY
    cdiv
    co
    #
    cc0
    wceq
    #
    @2
    wo
    #
    cX
    cY
    cF
    co
    cpi
    c2
    cdiv
    co
    #
    @6
    cneg
    cpr
    #
    wcel
    cX
    cZ
    cF
    co
    @7
    wcel
    #
    wph
    @4
    wn
    @2
    @5
    wb
    wph
    @3
    cc0
    wph
    cZ
    cY
    angrtmuld.3
    angrtmuld.2
    angrtmuld.6
    angrtmuld.5
    divne0d
    neneqd
    @4
    @2
    biorf
    syl
    wph
    vx
    vy
    cF
    cX
    cY
    ang.1
    angrtmuld.1
    angrtmuld.4
    angrtmuld.2
    angrtmuld.5
    angrteqvd
    wph
    @8
    cZ
    cX
    cdiv
    co
    #
    cre
    cfv
    #
    cc0
    wceq
    @3
    @1
    cmul
    co
    #
    cc0
    wceq
    @5
    wph
    vx
    vy
    cF
    cX
    cZ
    ang.1
    angrtmuld.1
    angrtmuld.4
    angrtmuld.3
    angrtmuld.6
    angrteqvd
    wph
    @10
    @11
    cc0
    wph
    @3
    @0
    cmul
    co
    #
    cre
    cfv
    @10
    @11
    wph
    @12
    @9
    cre
    wph
    cZ
    cY
    cX
    angrtmuld.3
    angrtmuld.2
    angrtmuld.1
    angrtmuld.5
    angrtmuld.4
    dmdcan2d
    fveq2d
    wph
    @3
    @0
    angrtmuld.7
    wph
    cY
    cX
    angrtmuld.2
    angrtmuld.1
    angrtmuld.4
    divcld
    #
    remul2d
    eqtr3d
    eqeq1d
    wph
    @3
    @1
    wph
    cZ
    cY
    angrtmuld.3
    angrtmuld.2
    angrtmuld.5
    divcld
    wph
    @1
    wph
    @0
    @13
    recld
    recnd
    mul0ord
    3bitrd
    3bitr4d
end
