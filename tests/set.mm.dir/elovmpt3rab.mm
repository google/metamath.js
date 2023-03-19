include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "eqidd.mm"
include "elovmpt3rab1.mm"

theorem elovmpt3rab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cT: class T
  let cU: class U
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  assume elovmpt3rab.o: |- O = ( x e. _V , y e. _V |-> ( z e. M |-> { a e. N | ph } ) )

  disjoint A a
  disjoint M a
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint N a
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint T z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint X a
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y a
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z a
  disjoint Z z
  assert |- ( ( M e. U /\ N e. T ) -> ( A e. ( ( X O Y ) ` Z ) -> ( ( X e. _V /\ Y e. _V ) /\ ( Z e. M /\ A e. N ) ) ) )

  proof
    wph
    vx
    vy
    vz
    cA
    cT
    cU
    cM
    cN
    cM
    cN
    cO
    cX
    cY
    cZ
    va
    elovmpt3rab.o
    vx
    cv
    cX
    wceq
    vy
    cv
    cY
    wceq
    wa
    #
    cM
    eqidd
    @0
    cN
    eqidd
    elovmpt3rab1
end
