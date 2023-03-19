include "wcel.mm"
include "wa.mm"
include "cismt.mm"
include "co.mm"
include "cv.mm"
include "wf1o.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cab.mm"
include "cvv.mm"
include "elex.mm"
include "cbs.mm"
include "cds.mm"
include "eqidd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "f1oeq123d.mm"
include "oveqd.mm"
include "eqeq2d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "df-ismt.mm"
include "cmap.mm"
include "ovex.mm"
include "wf.mm"
include "f1of.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "sylibr.mm"
include "adantr.mm"
include "abssi.mm"
include "ssexi.mm"
include "ovmpt2.mm"
include "syl2an.mm"
include "eleq2d.mm"
include "fex.mm"
include "sylancl.mm"
include "f1oeq1.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem isismt
  let cB: class B
  let cD: class D
  let cP: class P
  let cF: class F
  let cG: class G
  let cH: class H
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  assume isismt.b: |- B = ( Base ` G )
  assume isismt.p: |- P = ( Base ` H )
  assume isismt.d: |- D = ( dist ` G )
  assume isismt.m: |- .- = ( dist ` H )

  disjoint B a
  disjoint B b
  disjoint a b
  disjoint F a
  disjoint F b
  disjoint G a
  disjoint G b
  disjoint H a
  disjoint H b
  disjoint .- f
  disjoint .- g
  disjoint .- h
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint D f
  disjoint D g
  disjoint D h
  disjoint F f
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint H f
  disjoint H g
  disjoint H h
  disjoint P f
  disjoint P g
  disjoint P h
  assert |- ( ( G e. V /\ H e. W ) -> ( F e. ( G Ismt H ) <-> ( F : B -1-1-onto-> P /\ A. a e. B A. b e. B ( ( F ` a ) .- ( F ` b ) ) = ( a D b ) ) ) )

  proof
    cG
    cV
    wcel
    #
    cH
    cW
    wcel
    #
    wa
    #
    cF
    cG
    cH
    cismt
    co
    #
    wcel
    cF
    cB
    cP
    vf
    cv
    #
    wf1o
    #
    va
    cv
    #
    @4
    cfv
    #
    vb
    cv
    #
    @4
    cfv
    #
    c.mi
    co
    #
    @6
    @8
    cD
    co
    #
    wceq
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    wa
    #
    vf
    cab
    #
    wcel
    cB
    cP
    cF
    wf1o
    #
    @6
    cF
    cfv
    #
    @8
    cF
    cfv
    #
    c.mi
    co
    #
    @11
    wceq
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    wa
    #
    @2
    @3
    @15
    cF
    @0
    cG
    cvv
    wcel
    cH
    cvv
    wcel
    @3
    @15
    wceq
    @1
    cG
    cV
    elex
    cH
    cW
    elex
    vg
    vh
    cG
    cH
    cvv
    cvv
    vg
    cv
    #
    cbs
    cfv
    #
    vh
    cv
    #
    cbs
    cfv
    #
    @4
    wf1o
    #
    @7
    @9
    @25
    cds
    cfv
    #
    co
    #
    @6
    @8
    @23
    cds
    cfv
    #
    co
    #
    wceq
    #
    vb
    @24
    wral
    #
    va
    @24
    wral
    #
    wa
    #
    vf
    cab
    @15
    cismt
    cB
    @26
    @4
    wf1o
    #
    @29
    @11
    wceq
    #
    vb
    cB
    wral
    #
    va
    cB
    wral
    #
    wa
    #
    vf
    cab
    @23
    cG
    wceq
    #
    @35
    @40
    vf
    @41
    @27
    @36
    @34
    @39
    @41
    @24
    cB
    @26
    @26
    @4
    @4
    @41
    @4
    eqidd
    @41
    @24
    cG
    cbs
    cfv
    #
    cB
    @23
    cG
    cbs
    fveq2
    isismt.b
    syl6eqr
    #
    @41
    @26
    eqidd
    f1oeq123d
    @41
    @33
    @38
    va
    @24
    cB
    @43
    @41
    @32
    @37
    vb
    @24
    cB
    @43
    @41
    @31
    @11
    @29
    @41
    @30
    cD
    @6
    @8
    @41
    @30
    cG
    cds
    cfv
    cD
    @23
    cG
    cds
    fveq2
    isismt.d
    syl6eqr
    oveqd
    eqeq2d
    raleqbidv
    raleqbidv
    anbi12d
    abbidv
    @25
    cH
    wceq
    #
    @40
    @14
    vf
    @44
    @36
    @5
    @39
    @13
    @44
    cB
    cB
    @26
    cP
    @4
    @4
    @44
    @4
    eqidd
    @44
    cB
    eqidd
    @44
    @26
    cH
    cbs
    cfv
    #
    cP
    @25
    cH
    cbs
    fveq2
    isismt.p
    syl6eqr
    f1oeq123d
    @44
    @37
    @12
    va
    vb
    cB
    cB
    @44
    @29
    @10
    @11
    @44
    @28
    c.mi
    @7
    @9
    @44
    @28
    cH
    cds
    cfv
    c.mi
    @25
    cH
    cds
    fveq2
    isismt.m
    syl6eqr
    oveqd
    eqeq1d
    2ralbidv
    anbi12d
    abbidv
    vf
    vg
    vh
    va
    vb
    df-ismt
    @15
    cP
    cB
    cmap
    co
    #
    cP
    cB
    cmap
    ovex
    @14
    vf
    @46
    @5
    @4
    @46
    wcel
    #
    @13
    @5
    cB
    cP
    @4
    wf
    @47
    cB
    cP
    @4
    f1of
    cP
    cB
    @4
    cP
    @45
    cvv
    isismt.p
    cH
    cbs
    fvex
    eqeltri
    cB
    @42
    cvv
    isismt.b
    cG
    cbs
    fvex
    eqeltri
    #
    elmap
    sylibr
    adantr
    abssi
    ssexi
    ovmpt2
    syl2an
    eleq2d
    @14
    @22
    vf
    cF
    @16
    cF
    cvv
    wcel
    #
    @21
    @16
    cB
    cP
    cF
    wf
    cB
    cvv
    wcel
    @49
    cB
    cP
    cF
    f1of
    @48
    cB
    cP
    cvv
    cF
    fex
    sylancl
    adantr
    @4
    cF
    wceq
    #
    @5
    @16
    @13
    @21
    cB
    cP
    @4
    cF
    f1oeq1
    @50
    @12
    @20
    va
    vb
    cB
    cB
    @50
    @10
    @19
    @11
    @50
    @7
    @17
    @9
    @18
    c.mi
    @6
    @4
    cF
    fveq1
    @8
    @4
    cF
    fveq1
    oveq12d
    eqeq1d
    2ralbidv
    anbi12d
    elab3
    syl6bb
end
