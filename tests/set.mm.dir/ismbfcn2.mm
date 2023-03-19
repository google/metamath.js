include "cmpt.mm"
include "cmbf.mm"
include "wcel.mm"
include "cre.mm"
include "ccom.mm"
include "cim.mm"
include "wa.mm"
include "cfv.mm"
include "cc.mm"
include "wf.mm"
include "wb.mm"
include "eqid.mm"
include "fmptd.mm"
include "ismbfcn.mm"
include "syl.mm"
include "cv.mm"
include "eqidd.mm"
include "cr.mm"
include "ref.mm"
include "a1i.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "eleq1d.mm"
include "imf.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem ismbfcn2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume ismbfcn2.1: |- ( ( ph /\ x e. A ) -> B e. CC )

  disjoint A x
  disjoint ph x
  disjoint B y
  disjoint x y
  disjoint ph y
  assert |- ( ph -> ( ( x e. A |-> B ) e. MblFn <-> ( ( x e. A |-> ( Re ` B ) ) e. MblFn /\ ( x e. A |-> ( Im ` B ) ) e. MblFn ) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cmbf
    wcel
    #
    cre
    @0
    ccom
    #
    cmbf
    wcel
    #
    cim
    @0
    ccom
    #
    cmbf
    wcel
    #
    wa
    #
    vx
    cA
    cB
    cre
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    #
    vx
    cA
    cB
    cim
    cfv
    #
    cmpt
    #
    cmbf
    wcel
    #
    wa
    wph
    cA
    cc
    @0
    wf
    @1
    @6
    wb
    wph
    vx
    cA
    cB
    cc
    @0
    ismbfcn2.1
    @0
    eqid
    fmptd
    cA
    @0
    ismbfcn
    syl
    wph
    @3
    @9
    @5
    @12
    wph
    @2
    @8
    cmbf
    wph
    vx
    vy
    cA
    cc
    cB
    vy
    cv
    #
    cre
    cfv
    @7
    @0
    cre
    ismbfcn2.1
    wph
    @0
    eqidd
    #
    wph
    vy
    cc
    cr
    cre
    cc
    cr
    cre
    wf
    wph
    ref
    a1i
    feqmptd
    @13
    cB
    cre
    fveq2
    fmptco
    eleq1d
    wph
    @4
    @11
    cmbf
    wph
    vx
    vy
    cA
    cc
    cB
    @13
    cim
    cfv
    @10
    @0
    cim
    ismbfcn2.1
    @14
    wph
    vy
    cc
    cr
    cim
    cc
    cr
    cim
    wf
    wph
    imf
    a1i
    feqmptd
    @13
    cB
    cim
    fveq2
    fmptco
    eleq1d
    anbi12d
    bitrd
end
