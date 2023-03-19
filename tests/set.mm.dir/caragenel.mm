include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cdm.mm"
include "cuni.mm"
include "cpw.mm"
include "wral.mm"
include "crab.mm"
include "wa.mm"
include "ccaragen.mm"
include "come.mm"
include "caragenval.mm"
include "syl.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "wb.mm"
include "ineq2.mm"
include "fveq2d.mm"
include "difeq2.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "a1i.mm"
include "bitrd.mm"

theorem caragenel
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cO: class O
  let va: setvar a
  let ve: setvar e
  let vk: setvar k
  let vx: setvar x
  assume caragenel.o: |- ( ph -> O e. OutMeas )
  assume caragenel.s: |- S = ( CaraGen ` O )

  disjoint E a
  disjoint O a
  disjoint E e
  disjoint a e
  disjoint O e
  disjoint k x
  assert |- ( ph -> ( E e. S <-> ( E e. ~P U. dom O /\ A. a e. ~P U. dom O ( ( O ` ( a i^i E ) ) +e ( O ` ( a \ E ) ) ) = ( O ` a ) ) ) )

  proof
    wph
    cE
    cS
    wcel
    cE
    va
    cv
    #
    ve
    cv
    #
    cin
    #
    cO
    cfv
    #
    @0
    @1
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    @0
    cO
    cfv
    #
    wceq
    #
    va
    cO
    cdm
    cuni
    cpw
    #
    wral
    #
    ve
    @9
    crab
    #
    wcel
    #
    cE
    @9
    wcel
    @0
    cE
    cin
    #
    cO
    cfv
    #
    @0
    cE
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    @7
    wceq
    #
    va
    @9
    wral
    #
    wa
    #
    wph
    cS
    @11
    cE
    wph
    cS
    cO
    ccaragen
    cfv
    #
    @11
    caragenel.s
    wph
    cO
    come
    wcel
    @21
    @11
    wceq
    caragenel.o
    ve
    cO
    va
    caragenval
    syl
    syl5eq
    eleq2d
    @12
    @20
    wb
    wph
    @10
    @19
    ve
    cE
    @9
    @1
    cE
    wceq
    #
    @8
    @18
    va
    @9
    @22
    @6
    @17
    @7
    @22
    @3
    @14
    @5
    @16
    cxad
    @22
    @2
    @13
    cO
    @1
    cE
    @0
    ineq2
    fveq2d
    @22
    @4
    @15
    cO
    @1
    cE
    @0
    difeq2
    fveq2d
    oveq12d
    eqeq1d
    ralbidv
    elrab
    a1i
    bitrd
end
