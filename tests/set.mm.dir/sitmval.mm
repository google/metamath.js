include "cvv.mm"
include "wcel.mm"
include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "csitm.mm"
include "co.mm"
include "csitg.mm"
include "cdm.mm"
include "cv.mm"
include "cof.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cress.mm"
include "cfv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "elex.mm"
include "syl.mm"
include "cds.mm"
include "oveq1.mm"
include "dmeqd.mm"
include "fveq2.mm"
include "ofeq.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "mpt2eq123dv.mm"
include "oveq2.mm"
include "eqcomi.mm"
include "mp1i.mm"
include "fveq12d.mm"
include "df-sitm.mm"
include "ovex.mm"
include "dmex.mm"
include "mpt2ex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"

theorem sitmval
  let wph: wff ph
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let cM: class M
  let cV: class V
  let cW: class W
  let vm: setvar m
  let vw: setvar w
  assume sitmval.d: |- D = ( dist ` W )
  assume sitmval.1: |- ( ph -> W e. V )
  assume sitmval.2: |- ( ph -> M e. U. ran measures )

  disjoint f g
  disjoint M f
  disjoint M g
  disjoint W f
  disjoint W g
  disjoint m w
  disjoint D m
  disjoint D w
  disjoint f m
  disjoint f w
  disjoint g m
  disjoint g w
  disjoint M m
  disjoint M w
  disjoint W m
  disjoint W w
  assert |- ( ph -> ( W sitm M ) = ( f e. dom ( W sitg M ) , g e. dom ( W sitg M ) |-> ( ( ( RR*s |`s ( 0 [,] +oo ) ) sitg M ) ` ( f oF D g ) ) ) )

  proof
    wph
    cW
    cvv
    wcel
    #
    cM
    cmeas
    crn
    cuni
    #
    wcel
    cW
    cM
    csitm
    co
    vf
    vg
    cW
    cM
    csitg
    co
    #
    cdm
    #
    @3
    vf
    cv
    #
    vg
    cv
    #
    cD
    cof
    #
    co
    #
    cxrs
    cc0
    cpnf
    cicc
    co
    cress
    co
    #
    cM
    csitg
    co
    #
    cfv
    #
    cmpt2
    #
    wceq
    wph
    cW
    cV
    wcel
    @0
    sitmval.1
    cW
    cV
    elex
    syl
    sitmval.2
    vw
    vm
    cW
    cM
    cvv
    @1
    vf
    vg
    vw
    cv
    #
    vm
    cv
    #
    csitg
    co
    #
    cdm
    #
    @15
    @4
    @5
    @12
    cds
    cfv
    #
    cof
    #
    co
    #
    @8
    @13
    csitg
    co
    #
    cfv
    #
    cmpt2
    @11
    csitm
    vf
    vg
    cW
    @13
    csitg
    co
    #
    cdm
    #
    @22
    @4
    @5
    cW
    cds
    cfv
    #
    cof
    #
    co
    #
    @19
    cfv
    #
    cmpt2
    @12
    cW
    wceq
    #
    vf
    vg
    @15
    @15
    @20
    @22
    @22
    @26
    @27
    @14
    @21
    @12
    cW
    @13
    csitg
    oveq1
    dmeqd
    #
    @28
    @27
    @18
    @25
    @19
    @27
    @17
    @24
    @4
    @5
    @27
    @16
    @23
    wceq
    @17
    @24
    wceq
    @12
    cW
    cds
    fveq2
    @16
    @23
    ofeq
    syl
    oveqd
    fveq2d
    mpt2eq123dv
    @13
    cM
    wceq
    #
    vf
    vg
    @22
    @22
    @26
    @3
    @3
    @10
    @29
    @21
    @2
    @13
    cM
    cW
    csitg
    oveq2
    dmeqd
    #
    @30
    @29
    @25
    @7
    @19
    @9
    @13
    cM
    @8
    csitg
    oveq2
    @29
    @24
    @6
    @4
    @5
    @23
    cD
    wceq
    @24
    @6
    wceq
    @29
    cD
    @23
    sitmval.d
    eqcomi
    @23
    cD
    ofeq
    mp1i
    oveqd
    fveq12d
    mpt2eq123dv
    vw
    vf
    vg
    vm
    df-sitm
    vf
    vg
    @3
    @3
    @10
    @2
    cW
    cM
    csitg
    ovex
    dmex
    #
    @31
    mpt2ex
    ovmpt2
    syl2anc
end
