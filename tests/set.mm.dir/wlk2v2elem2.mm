include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "c2.mm"
include "cs2.mm"
include "fveq1i.mm"
include "cz.mm"
include "wcel.mm"
include "0z.mm"
include "s2fv0.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "cs1.mm"
include "cvv.mm"
include "prex.mm"
include "s1fv.mm"
include "cs3.mm"
include "s3fv0.mm"
include "s3fv1.mm"
include "preq12i.mm"
include "eqcomi.mm"
include "3eqtri.mm"
include "s2fv1.mm"
include "prcom.mm"
include "s3fv2.mm"
include "2wlklem.mm"
include "mpbir2an.mm"
include "cdm.mm"
include "cword.mm"
include "s2cli.mm"
include "eqeltri.mm"
include "wrddm.mm"
include "dmeqi.mm"
include "s2dm.mm"
include "raleqi.mm"
include "mpbir.mm"

theorem wlk2v2elem2
  let cP: class P
  let vk: setvar k
  let cF: class F
  let cI: class I
  let cX: class X
  let cY: class Y
  assume wlk2v2e.i: |- I = <" { X , Y } ">
  assume wlk2v2e.f: |- F = <" 0 0 ">
  assume wlk2v2e.x: |- X e. _V
  assume wlk2v2e.y: |- Y e. _V
  assume wlk2v2e.p: |- P = <" X Y X ">

  disjoint F k
  disjoint I k
  disjoint P k
  assert |- A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) }

  proof
    vk
    cv
    #
    cF
    cfv
    cI
    cfv
    @0
    cP
    cfv
    @0
    c1
    caddc
    co
    cP
    cfv
    cpr
    wceq
    #
    vk
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    wral
    @1
    vk
    cc0
    c1
    cpr
    #
    wral
    #
    @4
    cc0
    cF
    cfv
    #
    cI
    cfv
    #
    cc0
    cP
    cfv
    #
    c1
    cP
    cfv
    #
    cpr
    #
    wceq
    c1
    cF
    cfv
    #
    cI
    cfv
    #
    @8
    c2
    cP
    cfv
    #
    cpr
    #
    wceq
    @6
    cc0
    cI
    cfv
    #
    cX
    cY
    cpr
    #
    @9
    @5
    cc0
    cI
    @5
    cc0
    cc0
    cc0
    cs2
    #
    cfv
    #
    cc0
    cc0
    cF
    @16
    wlk2v2e.f
    fveq1i
    cc0
    cz
    wcel
    #
    @17
    cc0
    wceq
    0z
    cc0
    cc0
    cz
    s2fv0
    ax-mp
    eqtri
    fveq2i
    @14
    cc0
    @15
    cs1
    #
    cfv
    #
    @15
    cc0
    cI
    @19
    wlk2v2e.i
    fveq1i
    @15
    cvv
    wcel
    @20
    @15
    wceq
    cX
    cY
    prex
    @15
    cvv
    s1fv
    ax-mp
    eqtri
    #
    @9
    @15
    @7
    cX
    @8
    cY
    @7
    cc0
    cX
    cY
    cX
    cs3
    #
    cfv
    #
    cX
    cc0
    cP
    @22
    wlk2v2e.p
    fveq1i
    cX
    cvv
    wcel
    #
    @23
    cX
    wceq
    wlk2v2e.x
    cX
    cY
    cX
    cvv
    s3fv0
    ax-mp
    eqtri
    @8
    c1
    @22
    cfv
    #
    cY
    c1
    cP
    @22
    wlk2v2e.p
    fveq1i
    cY
    cvv
    wcel
    @25
    cY
    wceq
    wlk2v2e.y
    cX
    cY
    cX
    cvv
    s3fv1
    ax-mp
    eqtri
    #
    preq12i
    eqcomi
    3eqtri
    @11
    @14
    @15
    @13
    @10
    cc0
    cI
    @10
    c1
    @16
    cfv
    #
    cc0
    c1
    cF
    @16
    wlk2v2e.f
    fveq1i
    @18
    @27
    cc0
    wceq
    0z
    cc0
    cc0
    cz
    s2fv1
    ax-mp
    eqtri
    fveq2i
    @21
    @15
    cY
    cX
    cpr
    #
    @13
    cX
    cY
    prcom
    @13
    @28
    @8
    cY
    @12
    cX
    @26
    @12
    c2
    @22
    cfv
    #
    cX
    c2
    cP
    @22
    wlk2v2e.p
    fveq1i
    @24
    @29
    cX
    wceq
    wlk2v2e.x
    cX
    cY
    cX
    cvv
    s3fv2
    ax-mp
    eqtri
    preq12i
    eqcomi
    eqtri
    3eqtri
    cP
    vk
    cI
    cF
    2wlklem
    mpbir2an
    @1
    vk
    @2
    @3
    @2
    cF
    cdm
    #
    @16
    cdm
    @3
    @30
    @2
    cF
    cvv
    cword
    #
    wcel
    @30
    @2
    wceq
    cF
    @16
    @31
    wlk2v2e.f
    cc0
    cc0
    s2cli
    eqeltri
    cvv
    cF
    wrddm
    ax-mp
    eqcomi
    cF
    @16
    wlk2v2e.f
    dmeqi
    cc0
    cc0
    s2dm
    3eqtri
    raleqi
    mpbir
end
