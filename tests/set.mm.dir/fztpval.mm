include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "cif.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "ctp.mm"
include "w3a.mm"
include "caddc.mm"
include "cz.mm"
include "wcel.mm"
include "1z.mm"
include "fztp.mm"
include "ax-mp.mm"
include "df-3.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "addcomi.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "tpeq3.mm"
include "df-2.mm"
include "tpeq2.mm"
include "3eqtr4i.mm"
include "raleqi.mm"
include "1ex.mm"
include "2ex.mm"
include "3ex.mm"
include "fveq2.mm"
include "iftrue.mm"
include "eqeq12d.mm"
include "wne.mm"
include "1re.mm"
include "1lt2.mm"
include "gtneii.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "ifnefalse.mm"
include "syl.mm"
include "eqtrd.mm"
include "1lt3.mm"
include "2re.mm"
include "2lt3.mm"
include "raltp.mm"
include "bitri.mm"

theorem fztpval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  assert |- ( A. x e. ( 1 ... 3 ) ( F ` x ) = if ( x = 1 , A , if ( x = 2 , B , C ) ) <-> ( ( F ` 1 ) = A /\ ( F ` 2 ) = B /\ ( F ` 3 ) = C ) )

  proof
    vx
    cv
    #
    cF
    cfv
    #
    @0
    c1
    wceq
    #
    cA
    @0
    c2
    wceq
    #
    cB
    cC
    cif
    #
    cif
    #
    wceq
    #
    vx
    c1
    c3
    cfz
    co
    #
    wral
    @6
    vx
    c1
    c2
    c3
    ctp
    #
    wral
    c1
    cF
    cfv
    #
    cA
    wceq
    #
    c2
    cF
    cfv
    #
    cB
    wceq
    #
    c3
    cF
    cfv
    #
    cC
    wceq
    #
    w3a
    @6
    vx
    @7
    @8
    c1
    c1
    c2
    caddc
    co
    #
    cfz
    co
    #
    c1
    c1
    c1
    caddc
    co
    #
    @15
    ctp
    #
    @7
    @8
    c1
    cz
    wcel
    @16
    @18
    wceq
    1z
    c1
    fztp
    ax-mp
    c3
    @15
    c1
    cfz
    c3
    c2
    c1
    caddc
    co
    @15
    df-3
    c2
    c1
    2cn
    ax-1cn
    addcomi
    eqtri
    #
    oveq2i
    @8
    c1
    c2
    @15
    ctp
    #
    @18
    c3
    @15
    wceq
    @8
    @20
    wceq
    @19
    c3
    @15
    c1
    c2
    tpeq3
    ax-mp
    c2
    @17
    wceq
    @20
    @18
    wceq
    df-2
    c2
    @17
    c1
    @15
    tpeq2
    ax-mp
    eqtri
    3eqtr4i
    raleqi
    @6
    @10
    @12
    @14
    vx
    c1
    c2
    c3
    1ex
    2ex
    3ex
    @2
    @1
    @9
    @5
    cA
    @0
    c1
    cF
    fveq2
    @2
    cA
    @4
    iftrue
    eqeq12d
    @3
    @1
    @11
    @5
    cB
    @0
    c2
    cF
    fveq2
    @3
    @5
    @4
    cB
    @3
    @0
    c1
    wne
    #
    @5
    @4
    wceq
    #
    @3
    @21
    c2
    c1
    wne
    c1
    c2
    1re
    1lt2
    gtneii
    @0
    c2
    c1
    neeq1
    mpbiri
    @0
    c1
    cA
    @4
    ifnefalse
    #
    syl
    @3
    cB
    cC
    iftrue
    eqtrd
    eqeq12d
    @0
    c3
    wceq
    #
    @1
    @13
    @5
    cC
    @0
    c3
    cF
    fveq2
    @24
    @5
    @4
    cC
    @24
    @21
    @22
    @24
    @21
    c3
    c1
    wne
    c1
    c3
    1re
    1lt3
    gtneii
    @0
    c3
    c1
    neeq1
    mpbiri
    @23
    syl
    @24
    @0
    c2
    wne
    #
    @4
    cC
    wceq
    @24
    @25
    c3
    c2
    wne
    c2
    c3
    2re
    2lt3
    gtneii
    @0
    c3
    c2
    neeq1
    mpbiri
    @0
    c2
    cB
    cC
    ifnefalse
    syl
    eqtrd
    eqeq12d
    raltp
    bitri
end
