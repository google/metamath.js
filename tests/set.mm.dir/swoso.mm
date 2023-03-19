include "wss.mm"
include "wpo.mm"
include "swopo.mm"
include "poss.mm"
include "sylc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wo.mm"
include "weq.mm"
include "w3o.mm"
include "wn.mm"
include "wb.mm"
include "sselda.mm"
include "anim12dan.mm"
include "brdifun.mm"
include "syl.mm"
include "w3a.mm"
include "df-3an.mm"
include "sylan2br.mm"
include "expr.mm"
include "sylbird.mm"
include "orrd.mm"
include "3orcomb.mm"
include "df-3or.mm"
include "bitri.mm"
include "sylibr.mm"
include "issod.mm"

theorem swoso
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let c.lt: class .<
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  assume swoer.1: |- R = ( ( X X. X ) \ ( .< u. `' .< ) )
  assume swoer.2: |- ( ( ph /\ ( y e. X /\ z e. X ) ) -> ( y .< z -> -. z .< y ) )
  assume swoer.3: |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) ) -> ( x .< y -> ( x .< z \/ z .< y ) ) )
  assume swoso.4: |- ( ph -> Y C_ X )
  assume swoso.5: |- ( ( ph /\ ( x e. Y /\ y e. Y /\ x R y ) ) -> x = y )

  disjoint x y
  disjoint x z
  disjoint .< x
  disjoint y z
  disjoint .< y
  disjoint .< z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y x
  disjoint Y y
  disjoint u v
  disjoint u w
  disjoint R u
  disjoint v w
  disjoint R v
  disjoint R w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint X u
  assert |- ( ph -> .< Or Y )

  proof
    wph
    vx
    vy
    cY
    c.lt
    wph
    cY
    cX
    wss
    cX
    c.lt
    wpo
    cY
    c.lt
    wpo
    swoso.4
    wph
    vx
    vy
    vz
    cX
    c.lt
    swoer.2
    swoer.3
    swopo
    cY
    cX
    c.lt
    poss
    sylc
    wph
    vx
    cv
    #
    cY
    wcel
    #
    vy
    cv
    #
    cY
    wcel
    #
    wa
    #
    wa
    #
    @0
    @2
    c.lt
    wbr
    #
    @2
    @0
    c.lt
    wbr
    #
    wo
    #
    vx
    vy
    weq
    #
    wo
    #
    @6
    @9
    @7
    w3o
    #
    @5
    @8
    @9
    @5
    @8
    wn
    #
    @0
    @2
    cR
    wbr
    #
    @9
    @5
    @0
    cX
    wcel
    #
    @2
    cX
    wcel
    #
    wa
    @13
    @12
    wb
    wph
    @1
    @14
    @3
    @15
    wph
    cY
    cX
    @0
    swoso.4
    sselda
    wph
    cY
    cX
    @2
    swoso.4
    sselda
    anim12dan
    @0
    @2
    cR
    c.lt
    cX
    swoer.1
    brdifun
    syl
    wph
    @4
    @13
    @9
    @4
    @13
    wa
    wph
    @1
    @3
    @13
    w3a
    @9
    @1
    @3
    @13
    df-3an
    swoso.5
    sylan2br
    expr
    sylbird
    orrd
    @11
    @6
    @7
    @9
    w3o
    @10
    @6
    @9
    @7
    3orcomb
    @6
    @7
    @9
    df-3or
    bitri
    sylibr
    issod
end
