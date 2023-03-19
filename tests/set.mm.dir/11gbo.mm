include "c1.mm"
include "cdc.mm"
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
include "c6.mm"
include "c5.mm"
include "6p5e11.mm"
include "ceven.mm"
include "6even.mm"
include "5odd.mm"
include "epoo.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "c3.mm"
include "3prm.mm"
include "5prm.mm"
include "3odd.mm"
include "3pm3.2i.mm"
include "gbpart11.mm"
include "pm3.2i.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "3anbi1d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "rexbidv.mm"
include "3anbi2d.mm"
include "rspc2ev.mm"
include "mp3an.mm"
include "isgbo.mm"
include "mpbir2an.mm"

theorem 11gbo
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x


  assert |- ; 1 1 e. GoldbachOdd

  proof
    c1
    c1
    cdc
    #
    cgbo
    wcel
    @0
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
    @0
    @1
    @3
    caddc
    co
    #
    @5
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
    c6
    c5
    caddc
    co
    #
    @0
    codd
    6p5e11
    c6
    ceven
    wcel
    c5
    codd
    wcel
    #
    @14
    codd
    wcel
    6even
    5odd
    c6
    c5
    epoo
    mp2an
    eqeltrri
    c3
    cprime
    wcel
    #
    @16
    c3
    codd
    wcel
    #
    @17
    @6
    w3a
    #
    @0
    c3
    c3
    caddc
    co
    #
    @5
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
    @13
    3prm
    3prm
    c5
    cprime
    wcel
    @17
    @17
    @15
    w3a
    #
    @0
    @19
    c5
    caddc
    co
    #
    wceq
    #
    wa
    #
    @23
    5prm
    @24
    @26
    @17
    @17
    @15
    3odd
    3odd
    5odd
    3pm3.2i
    gbpart11
    pm3.2i
    @22
    @27
    vr
    c5
    cprime
    @5
    c5
    wceq
    #
    @18
    @24
    @21
    @26
    @28
    @6
    @15
    @17
    @17
    @5
    c5
    codd
    eleq1
    3anbi3d
    @28
    @20
    @25
    @0
    @5
    c5
    @19
    caddc
    oveq2
    eqeq2d
    anbi12d
    rspcev
    mp2an
    @12
    @23
    @17
    @4
    @6
    w3a
    #
    @0
    c3
    @3
    caddc
    co
    #
    @5
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
    @1
    c3
    wceq
    #
    @11
    @33
    vr
    cprime
    @34
    @7
    @29
    @10
    @32
    @34
    @2
    @17
    @4
    @6
    @1
    c3
    codd
    eleq1
    3anbi1d
    @34
    @9
    @31
    @0
    @34
    @8
    @30
    @5
    caddc
    @1
    c3
    @3
    caddc
    oveq1
    oveq1d
    eqeq2d
    anbi12d
    rexbidv
    @3
    c3
    wceq
    #
    @33
    @22
    vr
    cprime
    @35
    @29
    @18
    @32
    @21
    @35
    @4
    @17
    @17
    @6
    @3
    c3
    codd
    eleq1
    3anbi2d
    @35
    @31
    @20
    @0
    @35
    @30
    @19
    @5
    caddc
    @3
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
    @0
    vr
    vq
    vp
    isgbo
    mpbir2an
end
