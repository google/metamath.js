include "crg.mm"
include "wcel.mm"
include "czrh.mm"
include "cfv.mm"
include "zring.mm"
include "cmgp.mm"
include "cmhm.mm"
include "co.mm"
include "cpsgn.mm"
include "csymg.mm"
include "ccom.mm"
include "cfn.mm"
include "crh.mm"
include "eqid.mm"
include "zrhrhm.mm"
include "rhmmhm.mm"
include "syl.mm"
include "ccnfld.mm"
include "c1.mm"
include "cneg.mm"
include "cpr.mm"
include "cress.mm"
include "csubmnd.mm"
include "cghm.mm"
include "psgnghm2.mm"
include "ghmmhm.mm"
include "cz.mm"
include "wss.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "csubg.mm"
include "cnmsgnsubg.mm"
include "subgsubm.mm"
include "ax-mp.mm"
include "wb.mm"
include "cnring.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "unitsubm.mm"
include "subsubm.mm"
include "mp2b.mm"
include "mpbi.mm"
include "simpli.mm"
include "1z.mm"
include "neg1z.mm"
include "prssi.mm"
include "mp2an.mm"
include "csubrg.mm"
include "zsubrg.mm"
include "subrgsubm.mm"
include "zringmpg.mm"
include "eqcomi.mm"
include "mpbir2an.mm"
include "cvv.mm"
include "wceq.mm"
include "zex.mm"
include "ressabs.mm"
include "oveq1i.mm"
include "eqtr3i.mm"
include "resmhm2.mm"
include "sylancl.mm"
include "mhmco.mm"
include "syl2an.mm"

theorem zrhpsgnmhm
  let cA: class A
  let cR: class R


  assert |- ( ( R e. Ring /\ A e. Fin ) -> ( ( ZRHom ` R ) o. ( pmSgn ` A ) ) e. ( ( SymGrp ` A ) MndHom ( mulGrp ` R ) ) )

  proof
    cR
    crg
    wcel
    #
    cR
    czrh
    cfv
    #
    zring
    cmgp
    cfv
    #
    cR
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    cA
    cpsgn
    cfv
    #
    cA
    csymg
    cfv
    #
    @2
    cmhm
    co
    wcel
    #
    @1
    @5
    ccom
    @6
    @3
    cmhm
    co
    wcel
    cA
    cfn
    wcel
    #
    @0
    @1
    zring
    cR
    crh
    co
    wcel
    @4
    cR
    @1
    @1
    eqid
    zrhrhm
    zring
    cR
    @1
    @2
    @3
    @2
    eqid
    @3
    eqid
    rhmmhm
    syl
    @8
    @5
    @6
    ccnfld
    cmgp
    cfv
    #
    c1
    c1
    cneg
    #
    cpr
    #
    cress
    co
    #
    cmhm
    co
    wcel
    #
    @11
    @2
    csubmnd
    cfv
    wcel
    #
    @7
    @8
    @5
    @6
    @12
    cghm
    co
    wcel
    @13
    cA
    @6
    @12
    @5
    @6
    eqid
    @5
    eqid
    @12
    eqid
    psgnghm2
    @6
    @12
    @5
    ghmmhm
    syl
    @14
    @11
    @9
    csubmnd
    cfv
    #
    wcel
    #
    @11
    cz
    wss
    #
    @16
    @11
    cc
    cc0
    csn
    cdif
    #
    wss
    #
    @11
    @9
    @18
    cress
    co
    #
    csubmnd
    cfv
    wcel
    #
    @16
    @19
    wa
    #
    @11
    @20
    csubg
    cfv
    wcel
    @21
    @20
    @20
    eqid
    #
    cnmsgnsubg
    @11
    @20
    subgsubm
    ax-mp
    ccnfld
    crg
    wcel
    @18
    @15
    wcel
    @21
    @22
    wb
    cnring
    ccnfld
    @18
    @9
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    @9
    eqid
    #
    unitsubm
    @11
    @18
    @9
    @20
    @23
    subsubm
    mp2b
    mpbi
    simpli
    c1
    cz
    wcel
    @10
    cz
    wcel
    @17
    1z
    neg1z
    c1
    @10
    cz
    prssi
    mp2an
    #
    cz
    ccnfld
    csubrg
    cfv
    wcel
    cz
    @15
    wcel
    @14
    @16
    @17
    wa
    wb
    zsubrg
    cz
    ccnfld
    @9
    @24
    subrgsubm
    @11
    cz
    @9
    @2
    @9
    cz
    cress
    co
    #
    @2
    zringmpg
    eqcomi
    subsubm
    mp2b
    mpbir2an
    @6
    @2
    @12
    @5
    @11
    @26
    @11
    cress
    co
    #
    @12
    @2
    @11
    cress
    co
    cz
    cvv
    wcel
    @17
    @27
    @12
    wceq
    zex
    @25
    cz
    @11
    @9
    cvv
    ressabs
    mp2an
    @26
    @2
    @11
    cress
    zringmpg
    oveq1i
    eqtr3i
    resmhm2
    sylancl
    @6
    @2
    @3
    @1
    @5
    mhmco
    syl2an
end
