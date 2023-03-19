include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "crab.mm"
include "cae.mm"
include "wbr.mm"
include "cdm.mm"
include "cdif.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "cvv.mm"
include "wb.mm"
include "dmexg.mm"
include "uniexg.mm"
include "syl.mm"
include "syl5eqelr.mm"
include "rabexg.mm"
include "cv.mm"
include "wa.mm"
include "simpr.mm"
include "dmeqd.mm"
include "unieqd.mm"
include "simpl.mm"
include "difeq12d.mm"
include "fveq12d.mm"
include "eqeq1d.mm"
include "df-ae.mm"
include "brabga.mm"
include "mpancom.mm"
include "difeq1i.mm"
include "notrab.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "syl6bb.mm"

theorem braew
  let wph: wff ph
  let vx: setvar x
  let cM: class M
  let cO: class O
  let va: setvar a
  let vm: setvar m
  assume braew.1: |- U. dom M = O

  disjoint O x
  disjoint a m
  disjoint a x
  disjoint O a
  disjoint m x
  disjoint O m
  disjoint M a
  disjoint M m
  disjoint a ph
  disjoint m ph
  assert |- ( M e. U. ran measures -> ( { x e. O | ph } ae M <-> ( M ` { x e. O | -. ph } ) = 0 ) )

  proof
    cM
    cmeas
    crn
    cuni
    #
    wcel
    #
    wph
    vx
    cO
    crab
    #
    cM
    cae
    wbr
    #
    cM
    cdm
    #
    cuni
    #
    @2
    cdif
    #
    cM
    cfv
    #
    cc0
    wceq
    #
    wph
    wn
    vx
    cO
    crab
    #
    cM
    cfv
    #
    cc0
    wceq
    @2
    cvv
    wcel
    #
    @1
    @3
    @8
    wb
    @1
    cO
    cvv
    wcel
    @11
    @1
    cO
    @5
    cvv
    braew.1
    @1
    @4
    cvv
    wcel
    @5
    cvv
    wcel
    cM
    @0
    dmexg
    @4
    cvv
    uniexg
    syl
    syl5eqelr
    wph
    vx
    cO
    cvv
    rabexg
    syl
    vm
    cv
    #
    cdm
    #
    cuni
    #
    va
    cv
    #
    cdif
    #
    @12
    cfv
    #
    cc0
    wceq
    @8
    va
    vm
    @2
    cM
    cae
    cvv
    @0
    @15
    @2
    wceq
    #
    @12
    cM
    wceq
    #
    wa
    #
    @17
    @7
    cc0
    @20
    @16
    @6
    @12
    cM
    @18
    @19
    simpr
    #
    @20
    @14
    @5
    @15
    @2
    @20
    @13
    @4
    @20
    @12
    cM
    @21
    dmeqd
    unieqd
    @18
    @19
    simpl
    difeq12d
    fveq12d
    eqeq1d
    vm
    va
    df-ae
    brabga
    mpancom
    @7
    @10
    cc0
    @6
    @9
    cM
    @6
    cO
    @2
    cdif
    @9
    @5
    cO
    @2
    braew.1
    difeq1i
    wph
    vx
    cO
    notrab
    eqtri
    fveq2i
    eqeq1i
    syl6bb
end
