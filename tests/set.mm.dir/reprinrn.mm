include "cv.mm"
include "cin.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "wcel.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "wa.mm"
include "crn.mm"
include "wss.mm"
include "crepr.mm"
include "wf.mm"
include "fin.mm"
include "wfn.mm"
include "df-f.mm"
include "ffn.mm"
include "adantl.mm"
include "biantrurd.mm"
include "bicomd.mm"
include "syl5bb.mm"
include "pm5.32da.mm"
include "cvv.mm"
include "wb.mm"
include "cn.mm"
include "nnex.mm"
include "a1i.mm"
include "ssexd.mm"
include "inex1g.mm"
include "syl.mm"
include "ovex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "anbi1d.mm"
include "3bitr4d.mm"
include "crab.mm"
include "inss1.mm"
include "syl5ss.mm"
include "reprval.mm"
include "eleq2d.mm"
include "rabid.mm"
include "syl6bb.mm"
include "an32.mm"

theorem reprinrn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let vc: setvar c
  let vb: setvar b
  let vm: setvar m
  let va: setvar a
  let vs: setvar s
  assume reprval.a: |- ( ph -> A C_ NN )
  assume reprval.m: |- ( ph -> M e. ZZ )
  assume reprval.s: |- ( ph -> S e. NN0 )

  disjoint B c
  disjoint A c
  disjoint M c
  disjoint S c
  disjoint c ph
  disjoint A b
  disjoint A m
  disjoint b c
  disjoint b m
  disjoint c m
  disjoint M b
  disjoint M m
  disjoint S a
  disjoint S b
  disjoint S m
  disjoint S s
  disjoint a b
  disjoint a c
  disjoint a m
  disjoint a s
  disjoint b s
  disjoint c s
  disjoint m s
  disjoint b ph
  disjoint m ph
  disjoint ph s
  assert |- ( ph -> ( c e. ( ( A i^i B ) ( repr ` S ) M ) <-> ( c e. ( A ( repr ` S ) M ) /\ ran c C_ B ) ) )

  proof
    wph
    vc
    cv
    #
    cA
    cB
    cin
    #
    cc0
    cS
    cfzo
    co
    #
    cmap
    co
    #
    wcel
    #
    @2
    va
    cv
    @0
    cfv
    va
    csu
    cM
    wceq
    #
    wa
    #
    @0
    cA
    @2
    cmap
    co
    #
    wcel
    #
    @0
    crn
    cB
    wss
    #
    wa
    #
    @5
    wa
    #
    @0
    @1
    cM
    cS
    crepr
    cfv
    #
    co
    #
    wcel
    #
    @0
    cA
    cM
    @12
    co
    #
    wcel
    #
    @9
    wa
    #
    wph
    @4
    @10
    @5
    wph
    @2
    @1
    @0
    wf
    #
    @2
    cA
    @0
    wf
    #
    @9
    wa
    #
    @4
    @10
    @18
    @19
    @2
    cB
    @0
    wf
    #
    wa
    wph
    @20
    @2
    cA
    cB
    @0
    fin
    wph
    @19
    @21
    @9
    @21
    @0
    @2
    wfn
    #
    @9
    wa
    #
    wph
    @19
    wa
    #
    @9
    @2
    cB
    @0
    df-f
    @24
    @9
    @23
    @24
    @22
    @9
    @19
    @22
    wph
    @2
    cA
    @0
    ffn
    adantl
    biantrurd
    bicomd
    syl5bb
    pm5.32da
    syl5bb
    wph
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    @4
    @18
    wb
    wph
    cA
    cvv
    wcel
    #
    @25
    wph
    cA
    cn
    cvv
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    reprval.a
    ssexd
    #
    cA
    cB
    cvv
    inex1g
    syl
    cc0
    cS
    cfzo
    ovex
    #
    @1
    @2
    @0
    cvv
    cvv
    elmapg
    sylancl
    wph
    @8
    @19
    @9
    wph
    @27
    @26
    @8
    @19
    wb
    @28
    @29
    cA
    @2
    @0
    cvv
    cvv
    elmapg
    sylancl
    anbi1d
    3bitr4d
    anbi1d
    wph
    @14
    @0
    @5
    vc
    @3
    crab
    #
    wcel
    @6
    wph
    @13
    @30
    @0
    wph
    @1
    cS
    cM
    va
    vc
    wph
    @1
    cA
    cn
    cA
    cB
    inss1
    reprval.a
    syl5ss
    reprval.m
    reprval.s
    reprval
    eleq2d
    @5
    vc
    @3
    rabid
    syl6bb
    wph
    @17
    @8
    @5
    wa
    #
    @9
    wa
    @11
    wph
    @16
    @31
    @9
    wph
    @16
    @0
    @5
    vc
    @7
    crab
    #
    wcel
    @31
    wph
    @15
    @32
    @0
    wph
    cA
    cS
    cM
    va
    vc
    reprval.a
    reprval.m
    reprval.s
    reprval
    eleq2d
    @5
    vc
    @7
    rabid
    syl6bb
    anbi1d
    @8
    @5
    @9
    an32
    syl6bb
    3bitr4d
end
