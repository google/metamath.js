include "clf.mm"
include "wcel.mm"
include "cnmf.mm"
include "cfv.mm"
include "cr.mm"
include "chil.mm"
include "cabs.mm"
include "cno.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cif.mm"
include "wceq.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "eleq1.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "0lnfn.mm"
include "nmfn0.mm"
include "0re.mm"
include "eqeltri.mm"
include "pm3.2i.mm"
include "elimhyp.mm"
include "nmbdfnlbi.mm"
include "dedth.mm"
include "3impia.mm"

theorem nmbdfnlb
  let cA: class A
  let cT: class T


  assert |- ( ( T e. LinFn /\ ( normfn ` T ) e. RR /\ A e. ~H ) -> ( abs ` ( T ` A ) ) <_ ( ( normfn ` T ) x. ( normh ` A ) ) )

  proof
    cT
    clf
    wcel
    #
    cT
    cnmf
    cfv
    #
    cr
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    cT
    cfv
    #
    cabs
    cfv
    #
    @1
    cA
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @0
    @2
    wa
    #
    @3
    @8
    wi
    @3
    cA
    @9
    cT
    chil
    cc0
    csn
    cxp
    #
    cif
    #
    cfv
    #
    cabs
    cfv
    #
    @11
    cnmf
    cfv
    #
    @6
    cmul
    co
    #
    cle
    wbr
    #
    wi
    cT
    @10
    cT
    @11
    wceq
    #
    @8
    @16
    @3
    @17
    @5
    @13
    @7
    @15
    cle
    @17
    @4
    @12
    cabs
    cA
    cT
    @11
    fveq1
    fveq2d
    @17
    @1
    @14
    @6
    cmul
    cT
    @11
    cnmf
    fveq2
    #
    oveq1d
    breq12d
    imbi2d
    cA
    @11
    @9
    @11
    clf
    wcel
    #
    @14
    cr
    wcel
    #
    wa
    @10
    clf
    wcel
    #
    @10
    cnmf
    cfv
    #
    cr
    wcel
    #
    wa
    cT
    @10
    @17
    @0
    @19
    @2
    @20
    cT
    @11
    clf
    eleq1
    @17
    @1
    @14
    cr
    @18
    eleq1d
    anbi12d
    @10
    @11
    wceq
    #
    @21
    @19
    @23
    @20
    @10
    @11
    clf
    eleq1
    @24
    @22
    @14
    cr
    @10
    @11
    cnmf
    fveq2
    eleq1d
    anbi12d
    @21
    @23
    0lnfn
    @22
    cc0
    cr
    nmfn0
    0re
    eqeltri
    pm3.2i
    elimhyp
    nmbdfnlbi
    dedth
    3impia
end
