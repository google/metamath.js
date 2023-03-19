include "c6.mm"
include "cgbe.mm"
include "wcel.mm"
include "ceven.mm"
include "cv.mm"
include "codd.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cprime.mm"
include "wrex.mm"
include "6even.mm"
include "c3.mm"
include "3prm.mm"
include "3odd.mm"
include "gbpart6.mm"
include "3pm3.2i.mm"
include "eleq1.mm"
include "biidd.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "3anbi123d.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "mp3an.mm"
include "isgbe.mm"
include "mpbir2an.mm"

theorem 6gbe
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- 6 e. GoldbachEven

  proof
    c6
    cgbe
    wcel
    c6
    ceven
    wcel
    vp
    cv
    #
    codd
    wcel
    #
    vq
    cv
    #
    codd
    wcel
    #
    c6
    @0
    @2
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    #
    6even
    c3
    cprime
    wcel
    #
    @8
    c3
    codd
    wcel
    #
    @9
    c6
    c3
    c3
    caddc
    co
    #
    wceq
    #
    w3a
    #
    @7
    3prm
    3prm
    @9
    @9
    @11
    3odd
    3odd
    gbpart6
    3pm3.2i
    @6
    @12
    @9
    @3
    c6
    c3
    @2
    caddc
    co
    #
    wceq
    #
    w3a
    vp
    vq
    c3
    c3
    cprime
    cprime
    @0
    c3
    wceq
    #
    @1
    @9
    @3
    @3
    @5
    @14
    @0
    c3
    codd
    eleq1
    @15
    @3
    biidd
    @15
    @4
    @13
    c6
    @0
    c3
    @2
    caddc
    oveq1
    eqeq2d
    3anbi123d
    @2
    c3
    wceq
    #
    @9
    @9
    @3
    @9
    @14
    @11
    @16
    @9
    biidd
    @2
    c3
    codd
    eleq1
    @16
    @13
    @10
    c6
    @2
    c3
    c3
    caddc
    oveq2
    eqeq2d
    3anbi123d
    rspc2ev
    mp3an
    c6
    vq
    vp
    isgbe
    mpbir2an
end
