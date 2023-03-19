include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cioo.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "covol.mm"
include "cdm.mm"
include "wceq.mm"
include "ioombl.mm"
include "mblvol.mm"
include "mp1i.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "c0.mm"
include "wi.mm"
include "ltle.mm"
include "ancoms.mm"
include "imdistani.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "ioo0.mm"
include "syl2an.mm"
include "biimpar.mm"
include "cc0.mm"
include "fveq2.mm"
include "ovol0.mm"
include "syl6eq.mm"
include "0re.mm"
include "syl6eqel.mm"
include "3syl.mm"
include "cmin.mm"
include "ovolioo.mm"
include "3expa.mm"
include "resubcl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "simpr.mm"
include "simpl.mm"
include "ltlecasei.mm"

theorem ioovolcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( vol ` ( A (,) B ) ) e. RR )

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
    cioo
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
    @3
    cvol
    cdm
    wcel
    @4
    @5
    wceq
    @2
    cA
    cB
    ioombl
    @3
    mblvol
    mp1i
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
    @2
    cB
    cA
    cle
    wbr
    #
    wa
    @3
    c0
    wceq
    #
    @6
    @2
    @7
    @8
    @1
    @0
    @7
    @8
    wi
    cB
    cA
    ltle
    ancoms
    imdistani
    @2
    @9
    @8
    @0
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @9
    @8
    wb
    @1
    cA
    rexr
    cB
    rexr
    cA
    cB
    ioo0
    syl2an
    biimpar
    @9
    @5
    cc0
    cr
    @9
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
    3syl
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
    @10
    @5
    @11
    wceq
    cA
    cB
    ovolioo
    3expa
    @2
    @11
    cr
    wcel
    #
    @10
    @1
    @0
    @12
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
