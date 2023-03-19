include "cz.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "w3a.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wn.mm"
include "simp3.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "wi.mm"
include "wa.mm"
include "simp1.mm"
include "zssre.mm"
include "syl6ss.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "syl.mm"
include "simp2.mm"
include "zsupss.mm"
include "syl3anc.mm"
include "ssrexv.mm"
include "sylc.mm"
include "supub.mm"
include "mpd.mm"
include "sseldd.mm"
include "suprzcl2.mm"
include "lenltd.mm"
include "mpbird.mm"

theorem suprzub
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vz: setvar z
  let cM: class M
  let cZ: class Z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B n
  disjoint M x
  disjoint M y
  disjoint Z x
  assert |- ( ( A C_ ZZ /\ E. x e. ZZ A. y e. A y <_ x /\ B e. A ) -> B <_ sup ( A , RR , < ) )

  proof
    cA
    cz
    wss
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    vy
    cA
    wral
    vx
    cz
    wrex
    #
    cB
    cA
    wcel
    #
    w3a
    #
    cB
    cA
    cr
    clt
    csup
    #
    cle
    wbr
    @6
    cB
    clt
    wbr
    wn
    #
    @5
    @4
    @7
    @0
    @3
    @4
    simp3
    #
    @5
    vx
    vy
    vz
    cr
    cA
    cB
    clt
    cr
    clt
    wor
    @5
    ltso
    a1i
    @5
    cA
    cr
    wss
    @2
    @1
    clt
    wbr
    wn
    vy
    cA
    wral
    @1
    @2
    clt
    wbr
    @1
    vz
    cv
    clt
    wbr
    vz
    cA
    wrex
    wi
    vy
    cr
    wral
    wa
    #
    vx
    cA
    wrex
    #
    @9
    vx
    cr
    wrex
    @5
    cA
    cz
    cr
    @0
    @3
    @4
    simp1
    #
    zssre
    syl6ss
    #
    @5
    @0
    cA
    c0
    wne
    #
    @3
    @10
    @11
    @5
    @4
    @13
    @8
    cA
    cB
    ne0i
    syl
    #
    @0
    @3
    @4
    simp2
    #
    vx
    vy
    vz
    cA
    cr
    zsupss
    syl3anc
    @9
    vx
    cA
    cr
    ssrexv
    sylc
    supub
    mpd
    @5
    cB
    @6
    @5
    cA
    cr
    cB
    @12
    @8
    sseldd
    @5
    cA
    cr
    @6
    @12
    @5
    @0
    @13
    @3
    @6
    cA
    wcel
    @11
    @14
    @15
    vx
    vy
    cA
    suprzcl2
    syl3anc
    sseldd
    lenltd
    mpbird
end
