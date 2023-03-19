include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "wss.mm"
include "com.mm"
include "wral.mm"
include "crn.mm"
include "cint.mm"
include "wcel.mm"
include "wi.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wceq.mm"
include "suceq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "sseq12d.mm"
include "cbvralv.mm"
include "fveq1.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "rneq.mm"
include "inteqd.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "pweq.mm"
include "oveq1d.mm"
include "raleqdv.mm"
include "elab2g.mm"

theorem isfin3ds
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let cB: class B
  assume isfin3ds.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. b e. _om ( a ` suc b ) C_ ( a ` b ) -> |^| ran a e. ran a ) }

  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint A a
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint A b
  disjoint f g
  disjoint f x
  disjoint A f
  disjoint g x
  disjoint A g
  disjoint A x
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B g
  disjoint B x
  assert |- ( A e. V -> ( A e. F <-> A. f e. ( ~P A ^m _om ) ( A. x e. _om ( f ` suc x ) C_ ( f ` x ) -> |^| ran f e. ran f ) ) )

  proof
    vb
    cv
    #
    csuc
    #
    va
    cv
    #
    cfv
    #
    @0
    @2
    cfv
    #
    wss
    #
    vb
    com
    wral
    #
    @2
    crn
    #
    cint
    #
    @7
    wcel
    #
    wi
    #
    va
    vg
    cv
    #
    cpw
    #
    com
    cmap
    co
    #
    wral
    #
    vx
    cv
    #
    csuc
    #
    vf
    cv
    #
    cfv
    #
    @15
    @17
    cfv
    #
    wss
    #
    vx
    com
    wral
    #
    @17
    crn
    #
    cint
    #
    @22
    wcel
    #
    wi
    #
    vf
    cA
    cpw
    #
    com
    cmap
    co
    #
    wral
    #
    vg
    cA
    cF
    cV
    @14
    @25
    vf
    @13
    wral
    @11
    cA
    wceq
    #
    @28
    @10
    @25
    va
    vf
    @13
    @2
    @17
    wceq
    #
    @6
    @21
    @9
    @24
    @6
    @16
    @2
    cfv
    #
    @15
    @2
    cfv
    #
    wss
    #
    vx
    com
    wral
    @30
    @21
    @5
    @33
    vb
    vx
    com
    @0
    @15
    wceq
    #
    @3
    @31
    @4
    @32
    @34
    @1
    @16
    @2
    @0
    @15
    suceq
    fveq2d
    @0
    @15
    @2
    fveq2
    sseq12d
    cbvralv
    @30
    @33
    @20
    vx
    com
    @30
    @31
    @18
    @32
    @19
    @16
    @2
    @17
    fveq1
    @15
    @2
    @17
    fveq1
    sseq12d
    ralbidv
    syl5bb
    @30
    @8
    @23
    @7
    @22
    @30
    @7
    @22
    @2
    @17
    rneq
    #
    inteqd
    @35
    eleq12d
    imbi12d
    cbvralv
    @29
    @25
    vf
    @13
    @27
    @29
    @12
    @26
    com
    cmap
    @11
    cA
    pweq
    oveq1d
    raleqdv
    syl5bb
    isfin3ds.f
    elab2g
end
