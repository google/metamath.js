include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "simp1.mm"
include "simp2.mm"
include "ne0i.mm"
include "syl.mm"
include "sseldd.mm"
include "simp3.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "3jca.mm"
include "suprub.mm"
include "wb.mm"
include "suprleub.mm"
include "mpbird.mm"
include "suprcl.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem ubelsupr
  let vx: setvar x
  let cA: class A
  let cU: class U
  let vy: setvar y

  disjoint A x
  disjoint U x
  disjoint x y
  disjoint A y
  disjoint U y
  assert |- ( ( A C_ RR /\ U e. A /\ A. x e. A x <_ U ) -> U = sup ( A , RR , < ) )

  proof
    cA
    cr
    wss
    #
    cU
    cA
    wcel
    #
    vx
    cv
    #
    cU
    cle
    wbr
    #
    vx
    cA
    wral
    #
    w3a
    #
    cU
    cA
    cr
    clt
    csup
    #
    wceq
    cU
    @6
    cle
    wbr
    #
    @6
    cU
    cle
    wbr
    #
    @5
    @0
    cA
    c0
    wne
    #
    @2
    vy
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vy
    cr
    wrex
    #
    w3a
    #
    @1
    @7
    @5
    @0
    @9
    @13
    @0
    @1
    @4
    simp1
    #
    @5
    @1
    @9
    @0
    @1
    @4
    simp2
    #
    cA
    cU
    ne0i
    syl
    @5
    cU
    cr
    wcel
    #
    @4
    @13
    @5
    cA
    cr
    cU
    @15
    @16
    sseldd
    #
    @0
    @1
    @4
    simp3
    #
    @12
    @4
    vy
    cU
    cr
    @10
    cU
    wceq
    @11
    @3
    vx
    cA
    @10
    cU
    @2
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    3jca
    #
    @16
    vy
    vx
    cA
    cU
    suprub
    syl2anc
    @5
    @8
    @4
    @19
    @5
    @14
    @17
    @8
    @4
    wb
    @20
    @18
    vy
    vx
    vx
    cA
    cU
    suprleub
    syl2anc
    mpbird
    @5
    cU
    @6
    @18
    @5
    @14
    @6
    cr
    wcel
    @20
    vy
    vx
    cA
    suprcl
    syl
    letri3d
    mpbir2and
end
