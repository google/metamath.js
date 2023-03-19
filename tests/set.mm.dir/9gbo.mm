include "c9.mm"
include "cgbo.mm"
include "wcel.mm"
include "codd.mm"
include "cv.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cprime.mm"
include "wrex.mm"
include "c8.mm"
include "c1.mm"
include "df-9.mm"
include "ceven.mm"
include "8even.mm"
include "evenp1odd.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "c3.mm"
include "3prm.mm"
include "3odd.mm"
include "3pm3.2i.mm"
include "gbpart9.mm"
include "pm3.2i.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "3anbi1d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "rexbidv.mm"
include "3anbi2d.mm"
include "rspc2ev.mm"
include "mp3an.mm"
include "isgbo.mm"
include "mpbir2an.mm"

theorem 9gbo
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- 9 e. GoldbachOdd

  proof
    c9
    cgbo
    wcel
    c9
    codd
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
    vr
    cv
    #
    codd
    wcel
    #
    w3a
    #
    c9
    @0
    @2
    caddc
    co
    #
    @4
    caddc
    co
    #
    wceq
    #
    wa
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
    c9
    c8
    c1
    caddc
    co
    #
    codd
    df-9
    c8
    ceven
    wcel
    @13
    codd
    wcel
    8even
    c8
    evenp1odd
    ax-mp
    eqeltri
    c3
    cprime
    wcel
    #
    @14
    c3
    codd
    wcel
    #
    @15
    @5
    w3a
    #
    c9
    c3
    c3
    caddc
    co
    #
    @4
    caddc
    co
    #
    wceq
    #
    wa
    #
    vr
    cprime
    wrex
    #
    @12
    3prm
    3prm
    @14
    @15
    @15
    @15
    w3a
    #
    c9
    @17
    c3
    caddc
    co
    #
    wceq
    #
    wa
    #
    @21
    3prm
    @22
    @24
    @15
    @15
    @15
    3odd
    3odd
    3odd
    3pm3.2i
    gbpart9
    pm3.2i
    @20
    @25
    vr
    c3
    cprime
    @4
    c3
    wceq
    #
    @16
    @22
    @19
    @24
    @26
    @5
    @15
    @15
    @15
    @4
    c3
    codd
    eleq1
    3anbi3d
    @26
    @18
    @23
    c9
    @4
    c3
    @17
    caddc
    oveq2
    eqeq2d
    anbi12d
    rspcev
    mp2an
    @11
    @21
    @15
    @3
    @5
    w3a
    #
    c9
    c3
    @2
    caddc
    co
    #
    @4
    caddc
    co
    #
    wceq
    #
    wa
    #
    vr
    cprime
    wrex
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
    @10
    @31
    vr
    cprime
    @32
    @6
    @27
    @9
    @30
    @32
    @1
    @15
    @3
    @5
    @0
    c3
    codd
    eleq1
    3anbi1d
    @32
    @8
    @29
    c9
    @32
    @7
    @28
    @4
    caddc
    @0
    c3
    @2
    caddc
    oveq1
    oveq1d
    eqeq2d
    anbi12d
    rexbidv
    @2
    c3
    wceq
    #
    @31
    @20
    vr
    cprime
    @33
    @27
    @16
    @30
    @19
    @33
    @3
    @15
    @15
    @5
    @2
    c3
    codd
    eleq1
    3anbi2d
    @33
    @29
    @18
    c9
    @33
    @28
    @17
    @4
    caddc
    @2
    c3
    c3
    caddc
    oveq2
    oveq1d
    eqeq2d
    anbi12d
    rexbidv
    rspc2ev
    mp3an
    c9
    vr
    vq
    vp
    isgbo
    mpbir2an
end
