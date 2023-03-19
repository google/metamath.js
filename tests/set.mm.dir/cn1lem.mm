include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "crp.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "simpr.mm"
include "cle.mm"
include "simpll.mm"
include "syl2anc.mm"
include "cr.mm"
include "ffvelrni.mm"
include "syl.mm"
include "subcld.mm"
include "abscld.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "ralrimiva.mm"
include "weq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"

theorem cn1lem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  assume cn1lem.1: |- F : CC --> CC
  assume cn1lem.2: |- ( ( z e. CC /\ A e. CC ) -> ( abs ` ( ( F ` z ) - ( F ` A ) ) ) <_ ( abs ` ( z - A ) ) )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F y
  assert |- ( ( A e. CC /\ x e. RR+ ) -> E. y e. RR+ A. z e. CC ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( F ` z ) - ( F ` A ) ) ) < x ) )

  proof
    cA
    cc
    wcel
    #
    vx
    cv
    #
    crp
    wcel
    #
    wa
    #
    @2
    vz
    cv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @1
    clt
    wbr
    #
    @4
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @1
    clt
    wbr
    #
    wi
    #
    vz
    cc
    wral
    #
    @6
    vy
    cv
    #
    clt
    wbr
    #
    @12
    wi
    #
    vz
    cc
    wral
    #
    vy
    crp
    wrex
    @0
    @2
    simpr
    @3
    @13
    vz
    cc
    @3
    @4
    cc
    wcel
    #
    wa
    #
    @11
    @6
    cle
    wbr
    #
    @7
    @12
    @20
    @19
    @0
    @21
    @3
    @19
    simpr
    #
    @0
    @2
    @19
    simpll
    #
    cn1lem.2
    syl2anc
    @20
    @11
    cr
    wcel
    @6
    cr
    wcel
    @1
    cr
    wcel
    #
    @21
    @7
    wa
    @12
    wi
    @20
    @10
    @20
    @8
    @9
    @20
    @19
    @8
    cc
    wcel
    @22
    cc
    cc
    @4
    cF
    cn1lem.1
    ffvelrni
    syl
    @20
    @0
    @9
    cc
    wcel
    @23
    cc
    cc
    cA
    cF
    cn1lem.1
    ffvelrni
    syl
    subcld
    abscld
    @20
    @5
    @20
    @4
    cA
    @22
    @23
    subcld
    abscld
    @2
    @24
    @0
    @19
    @1
    rpre
    ad2antlr
    @11
    @6
    @1
    lelttr
    syl3anc
    mpand
    ralrimiva
    @18
    @14
    vy
    @1
    crp
    vy
    vx
    weq
    #
    @17
    @13
    vz
    cc
    @25
    @16
    @7
    @12
    @15
    @1
    @6
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
end
