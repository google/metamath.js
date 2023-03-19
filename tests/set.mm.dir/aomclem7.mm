include "cr1.mm"
include "cfv.mm"
include "wwe.mm"
include "cv.mm"
include "wex.mm"
include "aomclem6.mm"
include "fvex.mm"
include "weeq1.mm"
include "spcev.mm"
include "syl.mm"

theorem aomclem7
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume aomclem6.b: |- B = { <. a , b >. | E. c e. ( R1 ` U. dom z ) ( ( c e. b /\ -. c e. a ) /\ A. d e. ( R1 ` U. dom z ) ( d ( z ` U. dom z ) c -> ( d e. a <-> d e. b ) ) ) }
  assume aomclem6.c: |- C = ( a e. _V |-> sup ( ( y ` a ) , ( R1 ` dom z ) , B ) )
  assume aomclem6.d: |- D = recs ( ( a e. _V |-> ( C ` ( ( R1 ` dom z ) \ ran a ) ) ) )
  assume aomclem6.e: |- E = { <. a , b >. | |^| ( `' D " { a } ) e. |^| ( `' D " { b } ) }
  assume aomclem6.f: |- F = { <. a , b >. | ( ( rank ` a ) _E ( rank ` b ) \/ ( ( rank ` a ) = ( rank ` b ) /\ a ( z ` suc ( rank ` a ) ) b ) ) }
  assume aomclem6.g: |- G = ( if ( dom z = U. dom z , F , E ) i^i ( ( R1 ` dom z ) X. ( R1 ` dom z ) ) )
  assume aomclem6.h: |- H = recs ( ( z e. _V |-> G ) )
  assume aomclem6.a: |- ( ph -> A e. On )
  assume aomclem6.y: |- ( ph -> A. a e. ~P ( R1 ` A ) ( a =/= (/) -> ( y ` a ) e. ( ( ~P a i^i Fin ) \ { (/) } ) ) )

  disjoint y z
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint ph z
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A z
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint H z
  disjoint G d
  assert |- ( ph -> E. b b We ( R1 ` A ) )

  proof
    wph
    cA
    cr1
    cfv
    #
    cA
    cH
    cfv
    #
    wwe
    #
    @0
    vb
    cv
    #
    wwe
    #
    vb
    wex
    wph
    vy
    vz
    cA
    cB
    cC
    cD
    cE
    cF
    cG
    cH
    va
    vb
    vc
    vd
    aomclem6.b
    aomclem6.c
    aomclem6.d
    aomclem6.e
    aomclem6.f
    aomclem6.g
    aomclem6.h
    aomclem6.a
    aomclem6.y
    aomclem6
    @4
    @2
    vb
    @1
    cA
    cH
    fvex
    @0
    @3
    @1
    weeq1
    spcev
    syl
end
