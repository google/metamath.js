include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "oveq12.mm"
include "breqd.mm"
include "fveq2.mm"
include "oveqd.mm"
include "mptmpt2opabbrd.mm"

theorem mptmpt2opabovd
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cG: class G
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume mptmpt2opabbrd.g: |- ( ph -> G e. W )
  assume mptmpt2opabbrd.x: |- ( ph -> X e. ( A ` G ) )
  assume mptmpt2opabbrd.y: |- ( ph -> Y e. ( B ` G ) )
  assume mptmpt2opabbrd.v: |- ( ph -> { <. f , h >. | ps } e. V )
  assume mptmpt2opabbrd.r: |- ( ( ph /\ f ( D ` G ) h ) -> ps )
  assume mptmpt2opabovd.m: |- M = ( g e. _V |-> ( a e. ( A ` g ) , b e. ( B ` g ) |-> { <. f , h >. | ( f ( a ( C ` g ) b ) h /\ f ( D ` g ) h ) } ) )

  disjoint A a
  disjoint A b
  disjoint A g
  disjoint a b
  disjoint a g
  disjoint b g
  disjoint B a
  disjoint B b
  disjoint B g
  disjoint D a
  disjoint D b
  disjoint D g
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint a f
  disjoint a h
  disjoint b f
  disjoint b h
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint W g
  disjoint X a
  disjoint X b
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint Y a
  disjoint Y b
  disjoint Y f
  disjoint Y g
  disjoint Y h
  disjoint f ph
  disjoint h ph
  disjoint C a
  disjoint C b
  disjoint C g
  assert |- ( ph -> ( X ( M ` G ) Y ) = { <. f , h >. | ( f ( X ( C ` G ) Y ) h /\ f ( D ` G ) h ) } )

  proof
    wph
    wps
    vf
    cv
    #
    vh
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    vg
    cv
    #
    cC
    cfv
    #
    co
    #
    wbr
    @0
    @1
    cX
    cY
    cG
    cC
    cfv
    #
    co
    #
    wbr
    @0
    @1
    @2
    @3
    @7
    co
    #
    wbr
    cA
    cB
    cD
    vf
    vg
    vh
    cG
    cM
    cV
    cW
    cX
    cY
    va
    vb
    mptmpt2opabbrd.g
    mptmpt2opabbrd.x
    mptmpt2opabbrd.y
    mptmpt2opabbrd.v
    mptmpt2opabbrd.r
    @2
    cX
    wceq
    @3
    cY
    wceq
    wa
    @9
    @8
    @0
    @1
    @2
    cX
    @3
    cY
    @7
    oveq12
    breqd
    @4
    cG
    wceq
    #
    @6
    @9
    @0
    @1
    @10
    @5
    @7
    @2
    @3
    @4
    cG
    cC
    fveq2
    oveqd
    breqd
    mptmpt2opabovd.m
    mptmpt2opabbrd
end
