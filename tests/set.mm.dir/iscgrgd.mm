include "cdm.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cr.mm"
include "cpm.mm"
include "wcel.mm"
include "wbr.mm"
include "wf.mm"
include "wss.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "reex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "jca.mm"
include "biantrurd.mm"
include "fdm.mm"
include "syl.mm"
include "eqtr4d.mm"
include "wb.mm"
include "iscgrg.mm"
include "3bitr4rd.mm"

theorem iscgrgd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let c.sm: class .~
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let c.mi: class .-
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume iscgrg.p: |- P = ( Base ` G )
  assume iscgrg.m: |- .- = ( dist ` G )
  assume iscgrg.e: |- .~ = ( cgrG ` G )
  assume iscgrgd.g: |- ( ph -> G e. V )
  assume iscgrgd.d: |- ( ph -> D C_ RR )
  assume iscgrgd.a: |- ( ph -> A : D --> P )
  assume iscgrgd.b: |- ( ph -> B : D --> P )

  disjoint i j
  disjoint G i
  disjoint G j
  disjoint A i
  disjoint A j
  disjoint B i
  disjoint B j
  disjoint a b
  disjoint a g
  disjoint a i
  disjoint a j
  disjoint G a
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint G b
  disjoint g i
  disjoint g j
  disjoint G g
  disjoint .- a
  disjoint .- b
  disjoint .- g
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint P a
  disjoint P b
  disjoint P g
  assert |- ( ph -> ( A .~ B <-> A. i e. dom A A. j e. dom A ( ( A ` i ) .- ( A ` j ) ) = ( ( B ` i ) .- ( B ` j ) ) ) )

  proof
    wph
    cA
    cdm
    #
    cB
    cdm
    #
    wceq
    #
    vi
    cv
    #
    cA
    cfv
    vj
    cv
    #
    cA
    cfv
    c.mi
    co
    @3
    cB
    cfv
    @4
    cB
    cfv
    c.mi
    co
    wceq
    vj
    @0
    wral
    vi
    @0
    wral
    #
    wa
    #
    cA
    cP
    cr
    cpm
    co
    #
    wcel
    #
    cB
    @7
    wcel
    #
    wa
    #
    @6
    wa
    #
    @5
    cA
    cB
    c.sm
    wbr
    #
    wph
    @10
    @6
    wph
    @8
    @9
    wph
    cD
    cP
    cA
    wf
    #
    cD
    cr
    wss
    #
    @8
    iscgrgd.a
    iscgrgd.d
    cP
    cvv
    wcel
    #
    cr
    cvv
    wcel
    #
    @13
    @14
    wa
    @8
    cP
    cG
    cbs
    cfv
    cvv
    iscgrg.p
    cG
    cbs
    fvex
    eqeltri
    #
    reex
    cP
    cr
    cD
    cA
    cvv
    cvv
    elpm2r
    mpanl12
    syl2anc
    wph
    cD
    cP
    cB
    wf
    #
    @14
    @9
    iscgrgd.b
    iscgrgd.d
    @15
    @16
    @18
    @14
    wa
    @9
    @17
    reex
    cP
    cr
    cD
    cB
    cvv
    cvv
    elpm2r
    mpanl12
    syl2anc
    jca
    biantrurd
    wph
    @2
    @5
    wph
    @0
    cD
    @1
    wph
    @13
    @0
    cD
    wceq
    iscgrgd.a
    cD
    cP
    cA
    fdm
    syl
    wph
    @18
    @1
    cD
    wceq
    iscgrgd.b
    cD
    cP
    cB
    fdm
    syl
    eqtr4d
    biantrurd
    wph
    cG
    cV
    wcel
    @12
    @11
    wb
    iscgrgd.g
    cA
    cB
    cP
    c.sm
    vi
    vj
    cG
    c.mi
    cV
    iscgrg.p
    iscgrg.m
    iscgrg.e
    iscgrg
    syl
    3bitr4rd
end
