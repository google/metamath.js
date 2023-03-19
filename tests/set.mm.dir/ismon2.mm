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
include "ismon.mm"
include "wb.mm"
include "ccat.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simprr.mm"
include "simplr.mm"
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
include "oveq2.mm"
include "f1mpt.mm"
include "bitr3d.mm"
include "syl.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem ismon2
  let wph: wff ph
  let vz: setvar z
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cM: class M
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cK: class K
  let cZ: class Z
  assume ismon.b: |- B = ( Base ` C )
  assume ismon.h: |- H = ( Hom ` C )
  assume ismon.o: |- .x. = ( comp ` C )
  assume ismon.s: |- M = ( Mono ` C )
  assume ismon.c: |- ( ph -> C e. Cat )
  assume ismon.x: |- ( ph -> X e. B )
  assume ismon.y: |- ( ph -> Y e. B )

  disjoint g h
  disjoint g z
  disjoint B g
  disjoint h z
  disjoint B h
  disjoint B z
  disjoint g ph
  disjoint h ph
  disjoint ph z
  disjoint C g
  disjoint C h
  disjoint C z
  disjoint H g
  disjoint H h
  disjoint H z
  disjoint .x. g
  disjoint .x. h
  disjoint .x. z
  disjoint F g
  disjoint F h
  disjoint F z
  disjoint X g
  disjoint X h
  disjoint X z
  disjoint Y g
  disjoint Y h
  disjoint Y z
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint G g
  disjoint G h
  disjoint G z
  disjoint K g
  disjoint K h
  disjoint K z
  disjoint f ph
  disjoint ph x
  disjoint ph y
  disjoint C b
  disjoint C c
  disjoint C f
  disjoint C x
  disjoint C y
  disjoint H b
  disjoint H c
  disjoint H f
  disjoint H x
  disjoint H y
  disjoint .x. b
  disjoint .x. c
  disjoint .x. f
  disjoint .x. x
  disjoint .x. y
  disjoint F f
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y x
  disjoint Y y
  disjoint Z g
  disjoint Z h
  disjoint Z z
  disjoint M f
  assert |- ( ph -> ( F e. ( X M Y ) <-> ( F e. ( X H Y ) /\ A. z e. B A. g e. ( z H X ) A. h e. ( z H X ) ( ( F ( <. z , X >. .x. Y ) g ) = ( F ( <. z , X >. .x. Y ) h ) -> g = h ) ) ) )

  proof
    wph
    cF
    cX
    cY
    cM
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
    vz
    cv
    #
    cX
    cH
    co
    #
    cF
    vg
    cv
    #
    @1
    cX
    cop
    cY
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
    cF
    vh
    cv
    #
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
    cF
    cH
    cM
    cX
    cY
    ismon.b
    ismon.h
    ismon.o
    ismon.s
    ismon.c
    ismon.x
    ismon.y
    ismon
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
    @1
    cY
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
    @3
    cF
    cH
    @1
    cX
    cY
    ismon.b
    ismon.h
    ismon.o
    wph
    cC
    ccat
    wcel
    @0
    @20
    ismon.c
    ad2antrr
    @13
    @14
    @19
    simprl
    wph
    cX
    cB
    wcel
    @0
    @20
    ismon.x
    ad2antrr
    wph
    cY
    cB
    wcel
    @0
    @20
    ismon.y
    ad2antrr
    @13
    @14
    @19
    simprr
    wph
    @0
    @20
    simplr
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
    oveq2
    f1mpt
    baib
    bitr3d
    syl
    ralbidva
    pm5.32da
    bitrd
end
