include "c8.mm"
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
include "8even.mm"
include "c5.mm"
include "c3.mm"
include "5prm.mm"
include "3prm.mm"
include "5odd.mm"
include "3odd.mm"
include "5p3e8.mm"
include "eqcomi.mm"
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

theorem 8gbe
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- 8 e. GoldbachEven

  proof
    c8
    cgbe
    wcel
    c8
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
    c8
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
    8even
    c5
    cprime
    wcel
    c3
    cprime
    wcel
    c5
    codd
    wcel
    #
    c3
    codd
    wcel
    #
    c8
    c5
    c3
    caddc
    co
    #
    wceq
    #
    w3a
    #
    @7
    5prm
    3prm
    @8
    @9
    @11
    5odd
    3odd
    @10
    c8
    5p3e8
    eqcomi
    3pm3.2i
    @6
    @12
    @8
    @3
    c8
    c5
    @2
    caddc
    co
    #
    wceq
    #
    w3a
    vp
    vq
    c5
    c3
    cprime
    cprime
    @0
    c5
    wceq
    #
    @1
    @8
    @3
    @3
    @5
    @14
    @0
    c5
    codd
    eleq1
    @15
    @3
    biidd
    @15
    @4
    @13
    c8
    @0
    c5
    @2
    caddc
    oveq1
    eqeq2d
    3anbi123d
    @2
    c3
    wceq
    #
    @8
    @8
    @3
    @9
    @14
    @11
    @16
    @8
    biidd
    @2
    c3
    codd
    eleq1
    @16
    @13
    @10
    c8
    @2
    c3
    c5
    caddc
    oveq2
    eqeq2d
    3anbi123d
    rspc2ev
    mp3an
    c8
    vq
    vp
    isgbe
    mpbir2an
end
