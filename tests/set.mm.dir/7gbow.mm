include "c7.mm"
include "cgbow.mm"
include "wcel.mm"
include "codd.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "7odd.mm"
include "c2.mm"
include "2prm.mm"
include "c3.mm"
include "3prm.mm"
include "gbpart7.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "rexbidv.mm"
include "rspc2ev.mm"
include "mp3an.mm"
include "isgbow.mm"
include "mpbir2an.mm"

theorem 7gbow
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- 7 e. GoldbachOddW

  proof
    c7
    cgbow
    wcel
    c7
    codd
    wcel
    c7
    vp
    cv
    #
    vq
    cv
    #
    caddc
    co
    #
    vr
    cv
    #
    caddc
    co
    #
    wceq
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    vp
    cprime
    wrex
    #
    7odd
    c2
    cprime
    wcel
    #
    @8
    c7
    c2
    c2
    caddc
    co
    #
    @3
    caddc
    co
    #
    wceq
    #
    vr
    cprime
    wrex
    #
    @7
    2prm
    2prm
    c3
    cprime
    wcel
    c7
    @9
    c3
    caddc
    co
    #
    wceq
    #
    @12
    3prm
    gbpart7
    @11
    @14
    vr
    c3
    cprime
    @3
    c3
    wceq
    @10
    @13
    c7
    @3
    c3
    @9
    caddc
    oveq2
    eqeq2d
    rspcev
    mp2an
    @6
    @12
    c7
    c2
    @1
    caddc
    co
    #
    @3
    caddc
    co
    #
    wceq
    #
    vr
    cprime
    wrex
    vp
    vq
    c2
    c2
    cprime
    cprime
    @0
    c2
    wceq
    #
    @5
    @17
    vr
    cprime
    @18
    @4
    @16
    c7
    @18
    @2
    @15
    @3
    caddc
    @0
    c2
    @1
    caddc
    oveq1
    oveq1d
    eqeq2d
    rexbidv
    @1
    c2
    wceq
    #
    @17
    @11
    vr
    cprime
    @19
    @16
    @10
    c7
    @19
    @15
    @9
    @3
    caddc
    @1
    c2
    c2
    caddc
    oveq2
    oveq1d
    eqeq2d
    rexbidv
    rspc2ev
    mp3an
    c7
    vr
    vq
    vp
    isgbow
    mpbir2an
end
