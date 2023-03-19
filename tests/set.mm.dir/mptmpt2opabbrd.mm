include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "cmpt2.mm"
include "wcel.mm"
include "wceq.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "fveq2.mm"
include "breqd.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "mpt2eq123dv.mm"
include "adantl.mm"
include "elex.mm"
include "adantr.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "mpt2exga.mm"
include "mp1i.mm"
include "fvmptd.mm"
include "syl2anc.mm"
include "oveqd.mm"
include "ancom.mm"
include "opabbii.mm"
include "opabresex2d.mm"
include "syl5eqel.mm"
include "anbi1d.mm"
include "eqid.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem mptmpt2opabbrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let cA: class A
  let cB: class B
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
  assume mptmpt2opabbrd.1: |- ( ( a = X /\ b = Y ) -> ( ta <-> th ) )
  assume mptmpt2opabbrd.2: |- ( g = G -> ( ch <-> ta ) )
  assume mptmpt2opabbrd.m: |- M = ( g e. _V |-> ( a e. ( A ` g ) , b e. ( B ` g ) |-> { <. f , h >. | ( ch /\ f ( D ` g ) h ) } ) )

  disjoint g ta
  disjoint a th
  disjoint b th
  disjoint a b
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
  assert |- ( ph -> ( X ( M ` G ) Y ) = { <. f , h >. | ( th /\ f ( D ` G ) h ) } )

  proof
    wph
    cX
    cY
    cG
    cM
    cfv
    #
    co
    cX
    cY
    va
    vb
    cG
    cA
    cfv
    #
    cG
    cB
    cfv
    #
    wta
    vf
    cv
    #
    vh
    cv
    #
    cG
    cD
    cfv
    #
    wbr
    #
    wa
    #
    vf
    vh
    copab
    #
    cmpt2
    #
    co
    #
    wth
    @6
    wa
    #
    vf
    vh
    copab
    #
    wph
    @0
    @9
    cX
    cY
    wph
    cG
    cW
    wcel
    #
    @13
    @0
    @9
    wceq
    mptmpt2opabbrd.g
    mptmpt2opabbrd.g
    @13
    @13
    wa
    #
    vg
    cG
    va
    vb
    vg
    cv
    #
    cA
    cfv
    #
    @15
    cB
    cfv
    #
    wch
    @3
    @4
    @15
    cD
    cfv
    #
    wbr
    #
    wa
    #
    vf
    vh
    copab
    #
    cmpt2
    #
    @9
    cvv
    cM
    cvv
    cM
    vg
    cvv
    @22
    cmpt
    wceq
    @14
    mptmpt2opabbrd.m
    a1i
    @15
    cG
    wceq
    #
    @22
    @9
    wceq
    @14
    @23
    va
    vb
    @16
    @17
    @21
    @1
    @2
    @8
    @15
    cG
    cA
    fveq2
    @15
    cG
    cB
    fveq2
    @23
    @20
    @7
    vf
    vh
    @23
    wch
    wta
    @19
    @6
    mptmpt2opabbrd.2
    @23
    @18
    @5
    @3
    @4
    @15
    cG
    cD
    fveq2
    breqd
    anbi12d
    opabbidv
    mpt2eq123dv
    adantl
    @13
    cG
    cvv
    wcel
    @13
    cG
    cW
    elex
    adantr
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    wa
    @9
    cvv
    wcel
    @14
    @24
    @25
    cG
    cA
    fvex
    cG
    cB
    fvex
    pm3.2i
    va
    vb
    @1
    @2
    @8
    cvv
    cvv
    mpt2exga
    mp1i
    fvmptd
    syl2anc
    oveqd
    wph
    cX
    @1
    wcel
    cY
    @2
    wcel
    @12
    cvv
    wcel
    @10
    @12
    wceq
    mptmpt2opabbrd.x
    mptmpt2opabbrd.y
    wph
    @12
    @6
    wth
    wa
    #
    vf
    vh
    copab
    cvv
    @11
    @26
    vf
    vh
    wth
    @6
    ancom
    opabbii
    wph
    wps
    wth
    vf
    vh
    cG
    cV
    cD
    mptmpt2opabbrd.r
    mptmpt2opabbrd.v
    opabresex2d
    syl5eqel
    va
    vb
    cX
    cY
    @1
    @2
    @8
    @12
    @9
    cvv
    va
    cv
    cX
    wceq
    vb
    cv
    cY
    wceq
    wa
    #
    @7
    @11
    vf
    vh
    @27
    wta
    wth
    @6
    mptmpt2opabbrd.1
    anbi1d
    opabbidv
    @9
    eqid
    ovmpt2ga
    syl3anc
    eqtrd
end
