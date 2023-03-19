include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "isepi.mm"
include "wb.mm"
include "ccat.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simplr.mm"
include "simprr.mm"
include "catcocl.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "wf1.mm"
include "wf.mm"
include "eqid.mm"
include "fmpt.mm"
include "df-f1.mm"
include "baib.mm"
include "sylbi.mm"
include "oveq1.mm"
include "f1mpt.mm"
include "bitr3d.mm"
include "syl.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem isepi2
  let wph: wff ph
  let vz: setvar z
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cH: class H
  let cX: class X
  let cY: class Y
  let vf: setvar f
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
  disjoint g h
  disjoint H g
  disjoint h z
  disjoint H h
  disjoint H z
  disjoint .x. g
  disjoint .x. h
  disjoint .x. z
  disjoint X g
  disjoint X h
  disjoint X z
  disjoint F g
  disjoint F h
  disjoint F z
  disjoint g ph
  disjoint ph z
  disjoint Y g
  disjoint Y h
  disjoint Y z
  disjoint f g
  disjoint f h
  disjoint f z
  disjoint H f
  disjoint X f
  disjoint E f
  disjoint f ph
  disjoint Y f
  assert |- ( ph -> ( F e. ( X E Y ) <-> ( F e. ( X H Y ) /\ A. z e. B A. g e. ( Y H z ) A. h e. ( Y H z ) ( ( g ( <. X , Y >. .x. z ) F ) = ( h ( <. X , Y >. .x. z ) F ) -> g = h ) ) ) )

  proof
    wph
    cF
    cX
    cY
    cE
    co
    wcel
    cF
    cX
    cY
    cH
    co
    wcel
    #
    vg
    cY
    vz
    cv
    #
    cH
    co
    #
    vg
    cv
    #
    cF
    cX
    cY
    cop
    @1
    c.x
    co
    #
    co
    #
    cmpt
    #
    ccnv
    wfun
    #
    vz
    cB
    wral
    #
    wa
    @0
    @5
    vh
    cv
    #
    cF
    @4
    co
    #
    wceq
    @3
    @9
    wceq
    wi
    vh
    @2
    wral
    vg
    @2
    wral
    #
    vz
    cB
    wral
    #
    wa
    wph
    vz
    cB
    cC
    c.x
    vg
    cE
    cF
    cH
    cX
    cY
    isepi.b
    isepi.h
    isepi.o
    isepi.e
    isepi.c
    isepi.x
    isepi.y
    isepi
    wph
    @0
    @8
    @12
    wph
    @0
    wa
    #
    @7
    @11
    vz
    cB
    @13
    @1
    cB
    wcel
    #
    wa
    #
    @5
    cX
    @1
    cH
    co
    #
    wcel
    #
    vg
    @2
    wral
    #
    @7
    @11
    wb
    @15
    @17
    vg
    @2
    @13
    @14
    @3
    @2
    wcel
    #
    @17
    @13
    @14
    @19
    wa
    #
    wa
    cB
    cC
    c.x
    cF
    @3
    cH
    cX
    cY
    @1
    isepi.b
    isepi.h
    isepi.o
    wph
    cC
    ccat
    wcel
    @0
    @20
    isepi.c
    ad2antrr
    wph
    cX
    cB
    wcel
    @0
    @20
    isepi.x
    ad2antrr
    wph
    cY
    cB
    wcel
    @0
    @20
    isepi.y
    ad2antrr
    @13
    @14
    @19
    simprl
    wph
    @0
    @20
    simplr
    @13
    @14
    @19
    simprr
    catcocl
    anassrs
    ralrimiva
    @18
    @2
    @16
    @6
    wf1
    #
    @7
    @11
    @18
    @2
    @16
    @6
    wf
    #
    @21
    @7
    wb
    vg
    @2
    @16
    @5
    @6
    @6
    eqid
    #
    fmpt
    @21
    @22
    @7
    @2
    @16
    @6
    df-f1
    baib
    sylbi
    @21
    @18
    @11
    vg
    vh
    @2
    @16
    @5
    @10
    @6
    @23
    @3
    @9
    cF
    @4
    oveq1
    f1mpt
    baib
    bitr3d
    syl
    ralbidva
    pm5.32da
    bitrd
end
