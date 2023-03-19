include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cicc.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "covol.mm"
include "cdm.mm"
include "wceq.mm"
include "iccmbl.mm"
include "mblvol.mm"
include "syl.mm"
include "clt.mm"
include "wbr.mm"
include "c0.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "icc0.mm"
include "syl2an.mm"
include "biimpar.mm"
include "cc0.mm"
include "fveq2.mm"
include "ovol0.mm"
include "syl6eq.mm"
include "0re.mm"
include "syl6eqel.mm"
include "cle.mm"
include "cmin.mm"
include "ovolicc.mm"
include "3expa.mm"
include "resubcl.mm"
include "ancoms.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "simpr.mm"
include "simpl.mm"
include "ltlecasei.mm"

theorem iccvolcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( vol ` ( A [,] B ) ) e. RR )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cicc
    co
    #
    cvol
    cfv
    #
    @3
    covol
    cfv
    #
    cr
    @2
    @3
    cvol
    cdm
    wcel
    @4
    @5
    wceq
    cA
    cB
    iccmbl
    @3
    mblvol
    syl
    @2
    @5
    cr
    wcel
    #
    cB
    cA
    @2
    cB
    cA
    clt
    wbr
    #
    wa
    @3
    c0
    wceq
    #
    @6
    @2
    @8
    @7
    @0
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @8
    @7
    wb
    @1
    cA
    rexr
    cB
    rexr
    cA
    cB
    icc0
    syl2an
    biimpar
    @8
    @5
    cc0
    cr
    @8
    @5
    c0
    covol
    cfv
    cc0
    @3
    c0
    covol
    fveq2
    ovol0
    syl6eq
    0re
    syl6eqel
    syl
    @2
    cA
    cB
    cle
    wbr
    #
    wa
    @5
    cB
    cA
    cmin
    co
    #
    cr
    @0
    @1
    @9
    @5
    @10
    wceq
    cA
    cB
    ovolicc
    3expa
    @2
    @10
    cr
    wcel
    #
    @9
    @1
    @0
    @11
    cB
    cA
    resubcl
    ancoms
    adantr
    eqeltrd
    @0
    @1
    simpr
    @0
    @1
    simpl
    ltlecasei
    eqeltrd
end
