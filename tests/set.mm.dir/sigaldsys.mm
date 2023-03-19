include "csiga.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "cpw.mm"
include "c0.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "wss.mm"
include "sigasspw.mm"
include "selpw.mm"
include "sylibr.mm"
include "crn.mm"
include "elrnsiga.mm"
include "0elsiga.mm"
include "syl.mm"
include "adantr.mm"
include "baselsiga.mm"
include "simpr.mm"
include "difelsiga.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprl.mm"
include "sigaclcu.mm"
include "ex.mm"
include "3jca.mm"
include "jca.mm"
include "isldsys.mm"
include "ssriv.mm"

theorem sigaldsys
  let vx: setvar x
  let vy: setvar y
  let cL: class L
  let cO: class O
  let vs: setvar s
  let vu: setvar u
  let vt: setvar t
  let cS: class S
  let cV: class V
  assume isldsys.l: |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) }

  disjoint s y
  disjoint O s
  disjoint O x
  disjoint s x
  disjoint s u
  disjoint u y
  disjoint L t
  disjoint O t
  disjoint s t
  disjoint t x
  disjoint S s
  disjoint S x
  disjoint V x
  assert |- ( sigAlgebra ` O ) C_ L

  proof
    vt
    cO
    csiga
    cfv
    #
    cL
    vt
    cv
    #
    @0
    wcel
    #
    @1
    cO
    cpw
    #
    cpw
    wcel
    #
    c0
    @1
    wcel
    #
    cO
    vx
    cv
    #
    cdif
    @1
    wcel
    #
    vx
    @1
    wral
    #
    @6
    com
    cdom
    wbr
    #
    vy
    @6
    vy
    cv
    wdisj
    #
    wa
    #
    @6
    cuni
    @1
    wcel
    #
    wi
    #
    vx
    @1
    cpw
    #
    wral
    #
    w3a
    #
    wa
    @1
    cL
    wcel
    @2
    @4
    @16
    @2
    @1
    @3
    wss
    @4
    cO
    @1
    sigasspw
    vt
    @3
    selpw
    sylibr
    @2
    @5
    @8
    @15
    @2
    @1
    csiga
    crn
    cuni
    wcel
    #
    @5
    @1
    cO
    elrnsiga
    #
    @1
    0elsiga
    syl
    @2
    @7
    vx
    @1
    @2
    @6
    @1
    wcel
    #
    wa
    @17
    cO
    @1
    wcel
    #
    @19
    @7
    @2
    @17
    @19
    @18
    adantr
    @2
    @20
    @19
    cO
    @1
    baselsiga
    adantr
    @2
    @19
    simpr
    cO
    @6
    @1
    difelsiga
    syl3anc
    ralrimiva
    @2
    @13
    vx
    @14
    @2
    @6
    @14
    wcel
    #
    wa
    #
    @11
    @12
    @22
    @11
    wa
    @17
    @21
    @9
    @12
    @2
    @17
    @21
    @11
    @18
    ad2antrr
    @2
    @21
    @11
    simplr
    @22
    @9
    @10
    simprl
    @6
    @1
    sigaclcu
    syl3anc
    ex
    ralrimiva
    3jca
    jca
    vx
    vy
    @1
    cL
    cO
    vs
    isldsys.l
    isldsys
    sylibr
    ssriv
end
