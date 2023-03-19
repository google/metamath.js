include "cv.mm"
include "cdm.mm"
include "cuni.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "crab.mm"
include "cae.mm"
include "copab.mm"
include "cfae.mm"
include "wb.mm"
include "wceq.mm"
include "simpl.mm"
include "eleq1d.mm"
include "simpr.mm"
include "anbi12d.mm"
include "fveq1d.mm"
include "breq12d.mm"
include "rabbidv.mm"
include "breq1d.mm"
include "eqid.mm"
include "brabga.mm"
include "syl2anc.mm"
include "cvv.mm"
include "cmeas.mm"
include "crn.mm"
include "faeval.mm"
include "breqd.mm"
include "oveq1i.mm"
include "syl6eleqr.mm"
include "jca.mm"
include "biantrurd.mm"
include "3bitr4d.mm"

theorem brfae
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cM: class M
  let vf: setvar f
  let vg: setvar g
  assume brfae.0: |- dom R = D
  assume brfae.1: |- ( ph -> R e. _V )
  assume brfae.2: |- ( ph -> M e. U. ran measures )
  assume brfae.3: |- ( ph -> F e. ( D ^m U. dom M ) )
  assume brfae.4: |- ( ph -> G e. ( D ^m U. dom M ) )

  disjoint F x
  disjoint G x
  disjoint M x
  disjoint R x
  disjoint f g
  disjoint f x
  disjoint F f
  disjoint g x
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint M f
  disjoint M g
  disjoint R f
  disjoint R g
  assert |- ( ph -> ( F ( R ~ae M ) G <-> { x e. U. dom M | ( F ` x ) R ( G ` x ) } ae M ) )

  proof
    wph
    cF
    cG
    vf
    cv
    #
    cR
    cdm
    #
    cM
    cdm
    cuni
    #
    cmap
    co
    #
    wcel
    #
    vg
    cv
    #
    @3
    wcel
    #
    wa
    #
    vx
    cv
    #
    @0
    cfv
    #
    @8
    @5
    cfv
    #
    cR
    wbr
    #
    vx
    @2
    crab
    #
    cM
    cae
    wbr
    #
    wa
    #
    vf
    vg
    copab
    #
    wbr
    #
    cF
    @3
    wcel
    #
    cG
    @3
    wcel
    #
    wa
    #
    @8
    cF
    cfv
    #
    @8
    cG
    cfv
    #
    cR
    wbr
    #
    vx
    @2
    crab
    #
    cM
    cae
    wbr
    #
    wa
    #
    cF
    cG
    cR
    cM
    cfae
    co
    #
    wbr
    @24
    wph
    cF
    cD
    @2
    cmap
    co
    #
    wcel
    cG
    @27
    wcel
    @16
    @25
    wb
    brfae.3
    brfae.4
    @14
    @25
    vf
    vg
    cF
    cG
    @15
    @27
    @27
    @0
    cF
    wceq
    #
    @5
    cG
    wceq
    #
    wa
    #
    @7
    @19
    @13
    @24
    @30
    @4
    @17
    @6
    @18
    @30
    @0
    cF
    @3
    @28
    @29
    simpl
    #
    eleq1d
    @30
    @5
    cG
    @3
    @28
    @29
    simpr
    #
    eleq1d
    anbi12d
    @30
    @12
    @23
    cM
    cae
    @30
    @11
    @22
    vx
    @2
    @30
    @9
    @20
    @10
    @21
    cR
    @30
    @8
    @0
    cF
    @31
    fveq1d
    @30
    @8
    @5
    cG
    @32
    fveq1d
    breq12d
    rabbidv
    breq1d
    anbi12d
    @15
    eqid
    brabga
    syl2anc
    wph
    @26
    @15
    cF
    cG
    wph
    cR
    cvv
    wcel
    cM
    cmeas
    crn
    cuni
    wcel
    @26
    @15
    wceq
    brfae.1
    brfae.2
    vx
    cR
    vf
    vg
    cM
    faeval
    syl2anc
    breqd
    wph
    @19
    @24
    wph
    @17
    @18
    wph
    cF
    @27
    @3
    brfae.3
    @1
    cD
    @2
    cmap
    brfae.0
    oveq1i
    #
    syl6eleqr
    wph
    cG
    @27
    @3
    brfae.4
    @33
    syl6eleqr
    jca
    biantrurd
    3bitr4d
end
