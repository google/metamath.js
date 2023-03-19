include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "angvald.mm"
include "divcld.mm"
include "divne0d.mm"
include "logimclad.mm"
include "eqeltrd.mm"

theorem angcld
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
  assume angcld.1: |- ( ph -> X e. CC )
  assume angcld.2: |- ( ph -> X =/= 0 )
  assume angcld.3: |- ( ph -> Y e. CC )
  assume angcld.4: |- ( ph -> Y =/= 0 )

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
  assert |- ( ph -> ( X F Y ) e. ( -u _pi (,] _pi ) )

  proof
    wph
    cX
    cY
    cF
    co
    cY
    cX
    cdiv
    co
    #
    clog
    cfv
    cim
    cfv
    cpi
    cneg
    cpi
    cioc
    co
    wph
    vx
    vy
    cF
    cX
    cY
    ang.1
    angcld.1
    angcld.2
    angcld.3
    angcld.4
    angvald
    wph
    @0
    wph
    cY
    cX
    angcld.3
    angcld.1
    angcld.2
    divcld
    wph
    cY
    cX
    angcld.3
    angcld.1
    angcld.4
    angcld.2
    divne0d
    logimclad
    eqeltrd
end
