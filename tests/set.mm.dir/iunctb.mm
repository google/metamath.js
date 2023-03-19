include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "ciun.mm"
include "cxp.mm"
include "cv.mm"
include "csn.mm"
include "eqid.mm"
include "cmap.mm"
include "co.mm"
include "wacn.mm"
include "wcel.mm"
include "simpl.mm"
include "cvv.mm"
include "reldom.mm"
include "brrelexi.mm"
include "adantr.mm"
include "ovex.mm"
include "rgenw.mm"
include "iunexg.mm"
include "sylancl.mm"
include "acncc.mm"
include "syl6eleqr.mm"
include "acndom.mm"
include "sylc.mm"
include "simpr.mm"
include "cen.mm"
include "omex.mm"
include "xpdom1g.mm"
include "sylancr.mm"
include "xpomen.mm"
include "domentr.mm"
include "ccrd.mm"
include "cdm.mm"
include "ralimi.mm"
include "syl2an.mm"
include "con0.mm"
include "omelon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "numacn.mm"
include "mpisyl.mm"
include "acndom2.mm"
include "iundomg.mm"
include "domtr.mm"
include "syl2anc.mm"

theorem iunctb
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- ( ( A ~<_ _om /\ A. x e. A B ~<_ _om ) -> U_ x e. A B ~<_ _om )

  proof
    cA
    com
    cdom
    wbr
    #
    cB
    com
    cdom
    wbr
    #
    vx
    cA
    wral
    #
    wa
    #
    vx
    cA
    cB
    ciun
    #
    cA
    com
    cxp
    #
    cdom
    wbr
    @5
    com
    cdom
    wbr
    #
    @4
    com
    cdom
    wbr
    @3
    vx
    cA
    cB
    com
    vx
    cA
    vx
    cv
    csn
    cB
    cxp
    ciun
    #
    @7
    eqid
    @3
    @0
    vx
    cA
    com
    cB
    cmap
    co
    #
    ciun
    #
    com
    wacn
    #
    wcel
    @9
    cA
    wacn
    wcel
    @0
    @2
    simpl
    #
    @3
    @9
    cvv
    @10
    @3
    cA
    cvv
    wcel
    #
    @8
    cvv
    wcel
    #
    vx
    cA
    wral
    @9
    cvv
    wcel
    @0
    @12
    @2
    cA
    com
    cdom
    reldom
    brrelexi
    #
    adantr
    @13
    vx
    cA
    com
    cB
    cmap
    ovex
    rgenw
    vx
    cA
    @8
    cvv
    cvv
    iunexg
    sylancl
    acncc
    syl6eleqr
    cA
    com
    @9
    acndom
    sylc
    @0
    @2
    simpr
    @3
    @6
    com
    @4
    wacn
    #
    wcel
    #
    @5
    @15
    wcel
    @3
    @5
    com
    com
    cxp
    #
    cdom
    wbr
    #
    @17
    com
    cen
    wbr
    @6
    @3
    com
    cvv
    wcel
    @0
    @18
    omex
    @11
    cA
    com
    com
    cvv
    xpdom1g
    sylancr
    xpomen
    @5
    @17
    com
    domentr
    sylancl
    #
    @3
    @4
    cvv
    wcel
    #
    com
    ccrd
    cdm
    wcel
    #
    @16
    @0
    @12
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    @20
    @2
    @14
    @1
    @22
    vx
    cA
    cB
    com
    cdom
    reldom
    brrelexi
    ralimi
    vx
    cA
    cB
    cvv
    cvv
    iunexg
    syl2an
    com
    con0
    wcel
    @21
    omelon
    com
    onenon
    ax-mp
    @4
    cvv
    com
    numacn
    mpisyl
    @4
    @5
    com
    acndom2
    sylc
    iundomg
    @19
    @4
    @5
    com
    domtr
    syl2anc
end
