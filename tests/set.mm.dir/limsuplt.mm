include "cr.mm"
include "wss.mm"
include "cxr.mm"
include "wf.mm"
include "wcel.mm"
include "w3a.mm"
include "clsp.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wrex.mm"
include "clt.mm"
include "wral.mm"
include "limsuple.mm"
include "notbid.mm"
include "rexnal.mm"
include "syl6bbr.mm"
include "wb.mm"
include "cvv.mm"
include "simp2.mm"
include "reex.mm"
include "ssex.mm"
include "3ad2ant1.mm"
include "xrex.mm"
include "a1i.mm"
include "fex2.mm"
include "syl3anc.mm"
include "limsupcl.mm"
include "syl.mm"
include "simp3.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "limsupgf.mm"
include "ffvelrni.mm"
include "syl2anr.mm"
include "rexbidva.mm"
include "3bitr4d.mm"

theorem limsuplt
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let cM: class M
  let cC: class C
  assume limsupval.1: |- G = ( k e. RR |-> sup ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )

  disjoint F k
  disjoint A j
  disjoint B j
  disjoint j k
  disjoint F j
  disjoint G j
  disjoint k x
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F x
  disjoint f k
  disjoint G x
  disjoint M k
  disjoint C j
  disjoint C k
  disjoint C x
  disjoint j x
  assert |- ( ( B C_ RR /\ F : B --> RR* /\ A e. RR* ) -> ( ( limsup ` F ) < A <-> E. j e. RR ( G ` j ) < A ) )

  proof
    cB
    cr
    wss
    #
    cB
    cxr
    cF
    wf
    #
    cA
    cxr
    wcel
    #
    w3a
    #
    cA
    cF
    clsp
    cfv
    #
    cle
    wbr
    #
    wn
    #
    cA
    vj
    cv
    #
    cG
    cfv
    #
    cle
    wbr
    #
    wn
    #
    vj
    cr
    wrex
    #
    @4
    cA
    clt
    wbr
    #
    @8
    cA
    clt
    wbr
    #
    vj
    cr
    wrex
    @3
    @6
    @9
    vj
    cr
    wral
    #
    wn
    @11
    @3
    @5
    @14
    cA
    cB
    vj
    vk
    cF
    cG
    limsupval.1
    limsuple
    notbid
    @9
    vj
    cr
    rexnal
    syl6bbr
    @3
    @4
    cxr
    wcel
    #
    @2
    @12
    @6
    wb
    @3
    cF
    cvv
    wcel
    #
    @15
    @3
    @1
    cB
    cvv
    wcel
    #
    cxr
    cvv
    wcel
    #
    @16
    @0
    @1
    @2
    simp2
    @0
    @1
    @17
    @2
    cB
    cr
    reex
    ssex
    3ad2ant1
    @18
    @3
    xrex
    a1i
    cB
    cxr
    cF
    cvv
    cvv
    fex2
    syl3anc
    cF
    cvv
    limsupcl
    syl
    @0
    @1
    @2
    simp3
    #
    @4
    cA
    xrltnle
    syl2anc
    @3
    @13
    @10
    vj
    cr
    @7
    cr
    wcel
    @8
    cxr
    wcel
    @2
    @13
    @10
    wb
    @3
    cr
    cxr
    @7
    cG
    vk
    cF
    cG
    limsupval.1
    limsupgf
    ffvelrni
    @19
    @8
    cA
    xrltnle
    syl2anr
    rexbidva
    3bitr4d
end
