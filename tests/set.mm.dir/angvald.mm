include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "co.mm"
include "cdiv.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "wceq.mm"
include "angval.mm"
include "syl22anc.mm"

theorem angvald
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
  assume angvald.1: |- ( ph -> X e. CC )
  assume angvald.2: |- ( ph -> X =/= 0 )
  assume angvald.3: |- ( ph -> Y e. CC )
  assume angvald.4: |- ( ph -> Y =/= 0 )

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
  assert |- ( ph -> ( X F Y ) = ( Im ` ( log ` ( Y / X ) ) ) )

  proof
    wph
    cX
    cc
    wcel
    cX
    cc0
    wne
    cY
    cc
    wcel
    cY
    cc0
    wne
    cX
    cY
    cF
    co
    cY
    cX
    cdiv
    co
    clog
    cfv
    cim
    cfv
    wceq
    angvald.1
    angvald.2
    angvald.3
    angvald.4
    vx
    vy
    cX
    cY
    cF
    ang.1
    angval
    syl22anc
end
