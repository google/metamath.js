include "co.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "cneg.mm"
include "cpr.mm"
include "wcel.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "ccos.mm"
include "cc0.mm"
include "wceq.mm"
include "cre.mm"
include "angvald.mm"
include "eleq1d.mm"
include "cioc.mm"
include "wb.mm"
include "divcld.mm"
include "divne0d.mm"
include "logimclad.mm"
include "coseq0negpitopi.mm"
include "syl.mm"
include "cosarg0d.mm"
include "3bitr2d.mm"

theorem angrteqvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cX: class X
  let cY: class Y
  let cA: class A
  let cB: class B
  let cC: class C
  assume ang.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume angrteqvd.1: |- ( ph -> X e. CC )
  assume angrteqvd.2: |- ( ph -> X =/= 0 )
  assume angrteqvd.3: |- ( ph -> Y e. CC )
  assume angrteqvd.4: |- ( ph -> Y =/= 0 )

  disjoint x y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ph -> ( ( X F Y ) e. { ( _pi / 2 ) , -u ( _pi / 2 ) } <-> ( Re ` ( Y / X ) ) = 0 ) )

  proof
    wph
    cX
    cY
    cF
    co
    #
    cpi
    c2
    cdiv
    co
    #
    @1
    cneg
    cpr
    #
    wcel
    cY
    cX
    cdiv
    co
    #
    clog
    cfv
    cim
    cfv
    #
    @2
    wcel
    #
    @4
    ccos
    cfv
    cc0
    wceq
    #
    @3
    cre
    cfv
    cc0
    wceq
    wph
    @0
    @4
    @2
    wph
    vx
    vy
    cF
    cX
    cY
    ang.1
    angrteqvd.1
    angrteqvd.2
    angrteqvd.3
    angrteqvd.4
    angvald
    eleq1d
    wph
    @4
    cpi
    cneg
    cpi
    cioc
    co
    wcel
    @6
    @5
    wb
    wph
    @3
    wph
    cY
    cX
    angrteqvd.3
    angrteqvd.1
    angrteqvd.2
    divcld
    #
    wph
    cY
    cX
    angrteqvd.3
    angrteqvd.1
    angrteqvd.4
    angrteqvd.2
    divne0d
    #
    logimclad
    @4
    coseq0negpitopi
    syl
    wph
    @3
    @7
    @8
    cosarg0d
    3bitr2d
end
