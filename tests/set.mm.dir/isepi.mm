include "coppc.mm"
include "cfv.mm"
include "cmon.mm"
include "co.mm"
include "wcel.mm"
include "chom.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "wa.mm"
include "eqid.mm"
include "oppcbas.mm"
include "ccat.mm"
include "oppccat.mm"
include "syl.mm"
include "ismon.mm"
include "oppcmon.mm"
include "eleq2d.mm"
include "wceq.mm"
include "oppchom.mm"
include "a1i.mm"
include "simpr.mm"
include "adantr.mm"
include "oppcco.mm"
include "mpteq12dv.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "ralbidva.mm"
include "anbi12d.mm"
include "3bitr3d.mm"

theorem isepi
  let wph: wff ph
  let vz: setvar z
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cH: class H
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vh: setvar h
  assume isepi.b: |- B = ( Base ` C )
  assume isepi.h: |- H = ( Hom ` C )
  assume isepi.o: |- .x. = ( comp ` C )
  assume isepi.e: |- E = ( Epi ` C )
  assume isepi.c: |- ( ph -> C e. Cat )
  assume isepi.x: |- ( ph -> X e. B )
  assume isepi.y: |- ( ph -> Y e. B )

  disjoint g z
  disjoint B g
  disjoint B z
  disjoint C g
  disjoint C z
  disjoint H g
  disjoint H z
  disjoint .x. g
  disjoint .x. z
  disjoint X g
  disjoint X z
  disjoint F g
  disjoint F z
  disjoint g ph
  disjoint ph z
  disjoint Y g
  disjoint Y z
  disjoint f g
  disjoint f h
  disjoint f z
  disjoint H f
  disjoint g h
  disjoint h z
  disjoint H h
  disjoint .x. h
  disjoint X f
  disjoint X h
  disjoint E f
  disjoint F h
  disjoint f ph
  disjoint Y f
  disjoint Y h
  assert |- ( ph -> ( F e. ( X E Y ) <-> ( F e. ( X H Y ) /\ A. z e. B Fun `' ( g e. ( Y H z ) |-> ( g ( <. X , Y >. .x. z ) F ) ) ) ) )

  proof
    wph
    cF
    cY
    cX
    cC
    coppc
    cfv
    #
    cmon
    cfv
    #
    co
    #
    wcel
    cF
    cY
    cX
    @0
    chom
    cfv
    #
    co
    #
    wcel
    #
    vg
    vz
    cv
    #
    cY
    @3
    co
    #
    cF
    vg
    cv
    #
    @6
    cY
    cop
    cX
    @0
    cco
    cfv
    #
    co
    co
    #
    cmpt
    #
    ccnv
    #
    wfun
    #
    vz
    cB
    wral
    #
    wa
    cF
    cX
    cY
    cE
    co
    #
    wcel
    cF
    cX
    cY
    cH
    co
    #
    wcel
    #
    vg
    cY
    @6
    cH
    co
    #
    @8
    cF
    cX
    cY
    cop
    @6
    c.x
    co
    co
    #
    cmpt
    #
    ccnv
    #
    wfun
    #
    vz
    cB
    wral
    #
    wa
    wph
    vz
    cB
    @0
    @9
    vg
    cF
    @3
    @1
    cY
    cX
    cB
    cC
    @0
    @0
    eqid
    #
    isepi.b
    oppcbas
    @3
    eqid
    @9
    eqid
    @1
    eqid
    #
    wph
    cC
    ccat
    wcel
    @0
    ccat
    wcel
    isepi.c
    cC
    @0
    @24
    oppccat
    syl
    isepi.y
    isepi.x
    ismon
    wph
    @2
    @15
    cF
    wph
    cC
    cE
    @1
    @0
    cY
    cX
    @24
    isepi.c
    @25
    isepi.e
    oppcmon
    eleq2d
    wph
    @5
    @17
    @14
    @23
    wph
    @4
    @16
    cF
    @4
    @16
    wceq
    wph
    cC
    cH
    @0
    cY
    cX
    isepi.h
    @24
    oppchom
    a1i
    eleq2d
    wph
    @13
    @22
    vz
    cB
    wph
    @6
    cB
    wcel
    #
    wa
    #
    @12
    @21
    @27
    @11
    @20
    @27
    vg
    @7
    @10
    @18
    @19
    @7
    @18
    wceq
    @27
    cC
    cH
    @0
    @6
    cY
    isepi.h
    @24
    oppchom
    a1i
    @27
    cB
    cC
    c.x
    @8
    cF
    @0
    @6
    cY
    cX
    isepi.b
    isepi.o
    @24
    wph
    @26
    simpr
    wph
    cY
    cB
    wcel
    @26
    isepi.y
    adantr
    wph
    cX
    cB
    wcel
    @26
    isepi.x
    adantr
    oppcco
    mpteq12dv
    cnveqd
    funeqd
    ralbidva
    anbi12d
    3bitr3d
end
