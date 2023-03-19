include "cv.mm"
include "cdm.mm"
include "cr1.mm"
include "cfv.mm"
include "wor.mm"
include "cuni.mm"
include "cpw.mm"
include "cvv.mm"
include "wcel.mm"
include "wwe.mm"
include "fvex.mm"
include "wral.mm"
include "csuc.mm"
include "vex.mm"
include "dmex.mm"
include "uniex.mm"
include "sucid.mm"
include "syl5eleqr.mm"
include "wceq.mm"
include "fveq2.mm"
include "weeq12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "wepwso.mm"
include "sylancr.mm"
include "wb.mm"
include "fveq2d.mm"
include "con0.mm"
include "onuni.mm"
include "r1suc.mm"
include "3syl.mm"
include "eqtrd.mm"
include "soeq2.mm"
include "syl.mm"
include "mpbird.mm"

theorem aomclem1
  let wph: wff ph
  let vz: setvar z
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume aomclem1.b: |- B = { <. a , b >. | E. c e. ( R1 ` U. dom z ) ( ( c e. b /\ -. c e. a ) /\ A. d e. ( R1 ` U. dom z ) ( d ( z ` U. dom z ) c -> ( d e. a <-> d e. b ) ) ) }
  assume aomclem1.on: |- ( ph -> dom z e. On )
  assume aomclem1.su: |- ( ph -> dom z = suc U. dom z )
  assume aomclem1.we: |- ( ph -> A. a e. dom z ( z ` a ) We ( R1 ` a ) )

  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  assert |- ( ph -> B Or ( R1 ` dom z ) )

  proof
    wph
    vz
    cv
    #
    cdm
    #
    cr1
    cfv
    #
    cB
    wor
    #
    @1
    cuni
    #
    cr1
    cfv
    #
    cpw
    #
    cB
    wor
    #
    wph
    @5
    cvv
    wcel
    @5
    @4
    @0
    cfv
    #
    wwe
    #
    @7
    @4
    cr1
    fvex
    wph
    @4
    @1
    wcel
    va
    cv
    #
    cr1
    cfv
    #
    @10
    @0
    cfv
    #
    wwe
    #
    va
    @1
    wral
    @9
    wph
    @4
    @4
    csuc
    #
    @1
    @4
    @1
    @0
    vz
    vex
    dmex
    uniex
    sucid
    aomclem1.su
    syl5eleqr
    aomclem1.we
    @13
    @9
    va
    @4
    @1
    @10
    @4
    wceq
    @11
    @5
    @12
    @8
    @10
    @4
    @0
    fveq2
    @10
    @4
    cr1
    fveq2
    weeq12d
    rspcva
    syl2anc
    va
    vb
    vc
    vd
    @5
    @8
    cB
    cvv
    aomclem1.b
    wepwso
    sylancr
    wph
    @2
    @6
    wceq
    @3
    @7
    wb
    wph
    @2
    @14
    cr1
    cfv
    #
    @6
    wph
    @1
    @14
    cr1
    aomclem1.su
    fveq2d
    wph
    @1
    con0
    wcel
    @4
    con0
    wcel
    @15
    @6
    wceq
    aomclem1.on
    @1
    onuni
    @4
    r1suc
    3syl
    eqtrd
    @2
    @6
    cB
    soeq2
    syl
    mpbird
end
