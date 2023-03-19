include "clnr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "crg.mm"
include "eqid.mm"
include "islnr2.mm"
include "simprbi.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "sylan2.mm"
include "ancoms.mm"
include "wi.mm"
include "wss.mm"
include "lnrring.mm"
include "rspssid.mm"
include "sylan.mm"
include "ex.mm"
include "vex.mm"
include "elpw.mm"
include "3imtr4g.mm"
include "anim1d.mm"
include "elin.mm"
include "pweq.mm"
include "ineq1d.mm"
include "eleq2d.mm"
include "imbi2d.mm"
include "syl5ibrcom.mm"
include "imdistand.mm"
include "ancom.mm"
include "reximdv2.mm"
include "adantr.mm"
include "mpd.mm"

theorem lnr2i
  let cR: class R
  let cU: class U
  let vg: setvar g
  let cI: class I
  let cN: class N
  let vi: setvar i
  assume lnr2i.u: |- U = ( LIdeal ` R )
  assume lnr2i.n: |- N = ( RSpan ` R )

  disjoint I g
  disjoint N g
  disjoint R g
  disjoint U g
  disjoint I i
  disjoint g i
  disjoint N i
  disjoint R i
  disjoint U i
  assert |- ( ( R e. LNoeR /\ I e. U ) -> E. g e. ( ~P I i^i Fin ) I = ( N ` g ) )

  proof
    cR
    clnr
    wcel
    #
    cI
    cU
    wcel
    #
    wa
    cI
    vg
    cv
    #
    cN
    cfv
    #
    wceq
    #
    vg
    cR
    cbs
    cfv
    #
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @4
    vg
    cI
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @1
    @0
    @8
    @0
    @1
    vi
    cv
    #
    @3
    wceq
    #
    vg
    @7
    wrex
    #
    vi
    cU
    wral
    #
    @8
    @0
    cR
    crg
    wcel
    #
    @15
    @5
    cR
    cU
    vg
    vi
    cN
    @5
    eqid
    #
    lnr2i.u
    lnr2i.n
    islnr2
    simprbi
    @14
    @8
    vi
    cI
    cU
    @12
    cI
    wceq
    @13
    @4
    vg
    @7
    @12
    cI
    @3
    eqeq1
    rexbidv
    rspcva
    sylan2
    ancoms
    @0
    @8
    @11
    wi
    @1
    @0
    @4
    @4
    vg
    @7
    @10
    @0
    @4
    @2
    @7
    wcel
    #
    wa
    @4
    @2
    @10
    wcel
    #
    wa
    @18
    @4
    wa
    @19
    @4
    wa
    @0
    @4
    @18
    @19
    @0
    @18
    @19
    wi
    @4
    @18
    @2
    @3
    cpw
    #
    cfn
    cin
    #
    wcel
    #
    wi
    @0
    @2
    @6
    wcel
    #
    @2
    cfn
    wcel
    #
    wa
    @2
    @20
    wcel
    #
    @24
    wa
    @18
    @22
    @0
    @23
    @25
    @24
    @0
    @2
    @5
    wss
    #
    @2
    @3
    wss
    #
    @23
    @25
    @0
    @26
    @27
    @0
    @16
    @26
    @27
    cR
    lnrring
    @5
    cR
    @2
    cN
    lnr2i.n
    @17
    rspssid
    sylan
    ex
    @2
    @5
    vg
    vex
    #
    elpw
    @2
    @3
    @28
    elpw
    3imtr4g
    anim1d
    @2
    @6
    cfn
    elin
    @2
    @20
    cfn
    elin
    3imtr4g
    @4
    @19
    @22
    @18
    @4
    @10
    @21
    @2
    @4
    @9
    @20
    cfn
    cI
    @3
    pweq
    ineq1d
    eleq2d
    imbi2d
    syl5ibrcom
    imdistand
    @18
    @4
    ancom
    @19
    @4
    ancom
    3imtr4g
    reximdv2
    adantr
    mpd
end
