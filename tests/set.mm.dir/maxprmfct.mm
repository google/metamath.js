include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cprime.mm"
include "cdvds.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "prmz.mm"
include "ssriv.mm"
include "sstri.mm"
include "a1i.mm"
include "exprmfct.mm"
include "wex.mm"
include "wa.mm"
include "breq1.mm"
include "elrab2.mm"
include "exbii.mm"
include "n0.mm"
include "df-rex.mm"
include "3bitr4ri.mm"
include "sylib.mm"
include "eluzelz.mm"
include "cn.mm"
include "eluz2nn.mm"
include "anim1i.mm"
include "sylbi.mm"
include "wi.mm"
include "dvdsle.mm"
include "expcom.mm"
include "impd.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "syl.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "3jca.mm"
include "suprzcl2.mm"
include "jccir.mm"

theorem maxprmfct
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cN: class N
  assume maxprmfct.1: |- S = { z e. Prime | z || N }

  disjoint N x
  disjoint N y
  disjoint x y
  disjoint N z
  disjoint y z
  disjoint S x
  disjoint S y
  assert |- ( N e. ( ZZ>= ` 2 ) -> ( ( S C_ ZZ /\ S =/= (/) /\ E. x e. ZZ A. y e. S y <_ x ) /\ sup ( S , RR , < ) e. S ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    cS
    cz
    wss
    #
    cS
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cS
    wral
    #
    vx
    cz
    wrex
    #
    w3a
    cS
    cr
    clt
    csup
    cS
    wcel
    @0
    @1
    @2
    @7
    @1
    @0
    cS
    cprime
    cz
    cS
    vz
    cv
    #
    cN
    cdvds
    wbr
    #
    vz
    cprime
    crab
    cprime
    maxprmfct.1
    @9
    vz
    cprime
    ssrab2
    eqsstri
    vy
    cprime
    cz
    @3
    prmz
    #
    ssriv
    sstri
    a1i
    @0
    @3
    cN
    cdvds
    wbr
    #
    vy
    cprime
    wrex
    #
    @2
    cN
    vy
    exprmfct
    @3
    cS
    wcel
    #
    vy
    wex
    @3
    cprime
    wcel
    #
    @11
    wa
    #
    vy
    wex
    @2
    @12
    @13
    @15
    vy
    @9
    @11
    vz
    @3
    cprime
    cS
    @8
    @3
    cN
    cdvds
    breq1
    maxprmfct.1
    elrab2
    #
    exbii
    vy
    cS
    n0
    @11
    vy
    cprime
    df-rex
    3bitr4ri
    sylib
    @0
    cN
    cz
    wcel
    @3
    cN
    cle
    wbr
    #
    vy
    cS
    wral
    #
    @7
    c2
    cN
    eluzelz
    @0
    cN
    cn
    wcel
    #
    @18
    cN
    eluz2nn
    @19
    @17
    vy
    cS
    @13
    @3
    cz
    wcel
    #
    @11
    wa
    #
    @19
    @17
    @13
    @15
    @21
    @16
    @14
    @20
    @11
    @10
    anim1i
    sylbi
    @19
    @20
    @11
    @17
    @20
    @19
    @11
    @17
    wi
    @3
    cN
    dvdsle
    expcom
    impd
    syl5
    ralrimiv
    syl
    @6
    @18
    vx
    cN
    cz
    @4
    cN
    wceq
    @5
    @17
    vy
    cS
    @4
    cN
    @3
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    3jca
    vx
    vy
    cS
    suprzcl2
    jccir
end
