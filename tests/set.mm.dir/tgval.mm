include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wss.mm"
include "cab.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "wa.mm"
include "uniexg.mm"
include "abssexg.mm"
include "uniin.mm"
include "sstr.mm"
include "mpan2.mm"
include "ssin.mm"
include "sylibr.mm"
include "ss2abi.mm"
include "ssexg.mm"
include "mpan.mm"
include "3syl.mm"
include "ineq1.mm"
include "unieqd.mm"
include "sseq2d.mm"
include "abbidv.mm"
include "df-topgen.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem tgval
  let vx: setvar x
  let cB: class B
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cC: class C

  disjoint B x
  disjoint V x
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint V y
  disjoint V z
  disjoint C x
  disjoint C y
  assert |- ( B e. V -> ( topGen ` B ) = { x | x C_ U. ( B i^i ~P x ) } )

  proof
    cB
    cV
    wcel
    #
    cB
    cvv
    wcel
    vx
    cv
    #
    cB
    @1
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    vx
    cab
    #
    cvv
    wcel
    #
    cB
    ctg
    cfv
    @6
    wceq
    cB
    cV
    elex
    @0
    cB
    cuni
    #
    cvv
    wcel
    @1
    @8
    wss
    @1
    @2
    cuni
    #
    wss
    #
    wa
    #
    vx
    cab
    #
    cvv
    wcel
    #
    @7
    cB
    cV
    uniexg
    @10
    vx
    @8
    cvv
    abssexg
    @6
    @12
    wss
    @13
    @7
    @5
    @11
    vx
    @5
    @1
    @8
    @9
    cin
    #
    wss
    #
    @11
    @5
    @4
    @14
    wss
    @15
    cB
    @2
    uniin
    @1
    @4
    @14
    sstr
    mpan2
    @1
    @8
    @9
    ssin
    sylibr
    ss2abi
    @6
    @12
    cvv
    ssexg
    mpan
    3syl
    vy
    cB
    @1
    vy
    cv
    #
    @2
    cin
    #
    cuni
    #
    wss
    #
    vx
    cab
    @6
    cvv
    cvv
    ctg
    @16
    cB
    wceq
    #
    @19
    @5
    vx
    @20
    @18
    @4
    @1
    @20
    @17
    @3
    @16
    cB
    @2
    ineq1
    unieqd
    sseq2d
    abbidv
    vy
    vx
    df-topgen
    fvmptg
    syl2anc
end
