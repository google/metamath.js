include "co.mm"
include "wcel.mm"
include "cinv.mm"
include "cfv.mm"
include "cdm.mm"
include "csect.mm"
include "ccnv.mm"
include "cin.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "eqid.mm"
include "isoval.mm"
include "eleq2d.mm"
include "invfval.mm"
include "dmeqd.mm"
include "cop.mm"
include "cco.mm"
include "wex.mm"
include "cab.mm"
include "copab.mm"
include "sectfval.mm"
include "cnveqd.mm"
include "cnvopab.mm"
include "syl6eq.mm"
include "ineq12d.mm"
include "inopab.mm"
include "an4.mm"
include "an42.mm"
include "anidm.mm"
include "bitri.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "eqtri.mm"
include "dmopab.mm"
include "wb.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "elabg.mm"
include "syl.mm"
include "biantrurd.mm"
include "bicomd.mm"
include "a1i.mm"
include "eqcomd.mm"
include "oveqd.mm"
include "df-rex.mm"
include "syl6bbr.mm"
include "3bitrd.mm"

theorem dfiso2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cI: class I
  let c.as: class .*
  let cX: class X
  let cY: class Y
  let c.op: class .o.
  let vf: setvar f
  assume dfiso2.b: |- B = ( Base ` C )
  assume dfiso2.h: |- H = ( Hom ` C )
  assume dfiso2.c: |- ( ph -> C e. Cat )
  assume dfiso2.i: |- I = ( Iso ` C )
  assume dfiso2.x: |- ( ph -> X e. B )
  assume dfiso2.y: |- ( ph -> Y e. B )
  assume dfiso2.f: |- ( ph -> F e. ( X H Y ) )
  assume dfiso2.1: |- .1. = ( Id ` C )
  assume dfiso2.o: |- .o. = ( <. X , Y >. ( comp ` C ) X )
  assume dfiso2.p: |- .* = ( <. Y , X >. ( comp ` C ) Y )

  disjoint C g
  disjoint F g
  disjoint H g
  disjoint I g
  disjoint X g
  disjoint Y g
  disjoint .o. g
  disjoint .* g
  disjoint .1. g
  disjoint g ph
  disjoint C f
  disjoint f g
  disjoint F f
  disjoint H f
  disjoint X f
  disjoint Y f
  disjoint .1. f
  disjoint f ph
  assert |- ( ph -> ( F e. ( X I Y ) <-> E. g e. ( Y H X ) ( ( g .o. F ) = ( .1. ` X ) /\ ( F .* g ) = ( .1. ` Y ) ) ) )

  proof
    wph
    cF
    cX
    cY
    cI
    co
    #
    wcel
    cF
    cX
    cY
    cC
    cinv
    cfv
    #
    co
    #
    cdm
    #
    wcel
    cF
    cX
    cY
    cC
    csect
    cfv
    #
    co
    #
    cY
    cX
    @4
    co
    #
    ccnv
    #
    cin
    #
    cdm
    #
    wcel
    #
    vg
    cv
    #
    cF
    c.op
    co
    #
    cX
    c.1
    cfv
    #
    wceq
    #
    cF
    @11
    c.as
    co
    #
    cY
    c.1
    cfv
    #
    wceq
    #
    wa
    #
    vg
    cY
    cX
    cH
    co
    #
    wrex
    #
    wph
    @0
    @3
    cF
    wph
    cB
    cC
    cI
    @1
    cX
    cY
    dfiso2.b
    @1
    eqid
    #
    dfiso2.c
    dfiso2.x
    dfiso2.y
    dfiso2.i
    isoval
    eleq2d
    wph
    @3
    @9
    cF
    wph
    @2
    @8
    wph
    cB
    cC
    @4
    @1
    cX
    cY
    dfiso2.b
    @21
    dfiso2.c
    dfiso2.x
    dfiso2.y
    @4
    eqid
    #
    invfval
    dmeqd
    eleq2d
    wph
    @10
    cF
    vf
    cv
    #
    cX
    cY
    cH
    co
    #
    wcel
    #
    @11
    @19
    wcel
    #
    wa
    #
    @11
    @23
    cX
    cY
    cop
    cX
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    @13
    wceq
    #
    @23
    @11
    cY
    cX
    cop
    cY
    @28
    co
    #
    co
    #
    @16
    wceq
    #
    wa
    #
    wa
    #
    vg
    wex
    #
    vf
    cab
    #
    wcel
    #
    cF
    @24
    wcel
    #
    @26
    wa
    #
    @11
    cF
    @29
    co
    #
    @13
    wceq
    #
    cF
    @11
    @32
    co
    #
    @16
    wceq
    #
    wa
    #
    wa
    #
    vg
    wex
    #
    @20
    wph
    @9
    @38
    cF
    wph
    @9
    @36
    vf
    vg
    copab
    #
    cdm
    @38
    wph
    @8
    @49
    wph
    @8
    @27
    @31
    wa
    #
    vf
    vg
    copab
    #
    @26
    @25
    wa
    #
    @34
    wa
    #
    vf
    vg
    copab
    #
    cin
    #
    @49
    wph
    @5
    @51
    @7
    @54
    wph
    cB
    cC
    @4
    @28
    c.1
    vf
    vg
    cH
    cX
    cY
    dfiso2.b
    dfiso2.h
    @28
    eqid
    #
    dfiso2.1
    @22
    dfiso2.c
    dfiso2.x
    dfiso2.y
    sectfval
    wph
    @7
    @53
    vg
    vf
    copab
    #
    ccnv
    @54
    wph
    @6
    @57
    wph
    cB
    cC
    @4
    @28
    c.1
    vg
    vf
    cH
    cY
    cX
    dfiso2.b
    dfiso2.h
    @56
    dfiso2.1
    @22
    dfiso2.c
    dfiso2.y
    dfiso2.x
    sectfval
    cnveqd
    @53
    vg
    vf
    cnvopab
    syl6eq
    ineq12d
    @55
    @50
    @53
    wa
    #
    vf
    vg
    copab
    @49
    @50
    @53
    vf
    vg
    inopab
    @58
    @36
    vf
    vg
    @58
    @27
    @52
    wa
    #
    @35
    wa
    @36
    @27
    @31
    @52
    @34
    an4
    @59
    @27
    @35
    @59
    @27
    @27
    wa
    @27
    @25
    @26
    @26
    @25
    an42
    @27
    anidm
    bitri
    anbi1i
    bitri
    opabbii
    eqtri
    syl6eq
    dmeqd
    @36
    vf
    vg
    dmopab
    syl6eq
    eleq2d
    wph
    @40
    @39
    @48
    wb
    dfiso2.f
    @37
    @48
    vf
    cF
    @24
    @23
    cF
    wceq
    #
    @36
    @47
    vg
    @60
    @27
    @41
    @35
    @46
    @60
    @25
    @40
    @26
    @23
    cF
    @24
    eleq1
    anbi1d
    @60
    @31
    @43
    @34
    @45
    @60
    @30
    @42
    @13
    @23
    cF
    @11
    @29
    oveq2
    eqeq1d
    @60
    @33
    @44
    @16
    @23
    cF
    @11
    @32
    oveq1
    eqeq1d
    anbi12d
    anbi12d
    exbidv
    elabg
    syl
    wph
    @48
    @26
    @18
    wa
    #
    vg
    wex
    @20
    wph
    @47
    @61
    vg
    wph
    @41
    @26
    @46
    @18
    wph
    @26
    @41
    wph
    @40
    @26
    dfiso2.f
    biantrurd
    bicomd
    wph
    @43
    @14
    @45
    @17
    wph
    @42
    @12
    @13
    wph
    @29
    c.op
    @11
    cF
    wph
    c.op
    @29
    c.op
    @29
    wceq
    wph
    dfiso2.o
    a1i
    eqcomd
    oveqd
    eqeq1d
    wph
    @44
    @15
    @16
    wph
    @32
    c.as
    cF
    @11
    wph
    c.as
    @32
    c.as
    @32
    wceq
    wph
    dfiso2.p
    a1i
    eqcomd
    oveqd
    eqeq1d
    anbi12d
    anbi12d
    exbidv
    @18
    vg
    @19
    df-rex
    syl6bbr
    3bitrd
    3bitrd
end
