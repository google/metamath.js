include "cprime.mm"
include "wcel.mm"
include "c4.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "csqrt.mm"
include "cfl.mm"
include "cle.mm"
include "w3a.mm"
include "c6.mm"
include "c5.mm"
include "cdc.mm"
include "wceq.mm"
include "c1.mm"
include "c2.mm"
include "c9.mm"
include "c3.mm"
include "w3o.mm"
include "fmtno4prmfac.mm"
include "wi.mm"
include "cmul.mm"
include "co.mm"
include "5nn.mm"
include "1nn0.mm"
include "3nn.mm"
include "decnncl.mm"
include "1lt5.mm"
include "1nn.mm"
include "3nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "eqid.mm"
include "nprmi.mm"
include "id.mm"
include "5nn0.mm"
include "caddc.mm"
include "5cn.mm"
include "mulid1i.mm"
include "oveq1i.mm"
include "5p1e6.mm"
include "eqtri.mm"
include "5t3e15.mm"
include "decmul2c.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "pm2.21d.mm"
include "4nn0.mm"
include "4nn.mm"
include "1lt3.mm"
include "9nn0.mm"
include "4t3e12.mm"
include "3t3e9.mm"
include "decmul1.mm"
include "ax-1.mm"
include "3jaoi.mm"
include "com12.mm"
include "3ad2ant1.mm"
include "mpd.mm"

theorem fmtno4prmfac193
  let cP: class P
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( P e. Prime /\ P || ( FermatNo ` 4 ) /\ P <_ ( |_ ` ( sqrt ` ( FermatNo ` 4 ) ) ) ) -> P = ; ; 1 9 3 )

  proof
    cP
    cprime
    wcel
    #
    cP
    c4
    cfmtno
    cfv
    #
    cdvds
    wbr
    #
    cP
    @1
    csqrt
    cfv
    cfl
    cfv
    cle
    wbr
    #
    w3a
    cP
    c6
    c5
    cdc
    #
    wceq
    #
    cP
    c1
    c2
    cdc
    #
    c9
    cdc
    #
    wceq
    #
    cP
    c1
    c9
    cdc
    c3
    cdc
    wceq
    #
    w3o
    #
    @9
    cP
    fmtno4prmfac
    @0
    @2
    @10
    @9
    wi
    @3
    @10
    @0
    @9
    @5
    @0
    @9
    wi
    @8
    @9
    @5
    @0
    @9
    @5
    @0
    c5
    c1
    c3
    cdc
    #
    cmul
    co
    #
    cprime
    wcel
    c5
    @11
    @12
    5nn
    c1
    c3
    1nn0
    3nn
    decnncl
    1lt5
    c1
    c3
    c1
    1nn
    3nn0
    1nn0
    1lt10
    declti
    @12
    eqid
    nprmi
    @5
    cP
    @12
    cprime
    @5
    cP
    @4
    @12
    @5
    id
    c1
    c3
    c6
    c5
    c5
    c1
    @11
    5nn0
    1nn0
    3nn0
    @11
    eqid
    5nn0
    1nn0
    c5
    c1
    cmul
    co
    #
    c1
    caddc
    co
    c5
    c1
    caddc
    co
    c6
    @13
    c5
    c1
    caddc
    c5
    5cn
    mulid1i
    oveq1i
    5p1e6
    eqtri
    5t3e15
    decmul2c
    syl6eqr
    eleq1d
    mtbiri
    pm2.21d
    @8
    @0
    @9
    @8
    @0
    c4
    c3
    cdc
    #
    c3
    cmul
    co
    #
    cprime
    wcel
    @14
    c3
    @15
    c4
    c3
    4nn0
    3nn
    decnncl
    3nn
    c4
    c3
    c1
    4nn
    3nn0
    1nn0
    1lt10
    declti
    1lt3
    @15
    eqid
    nprmi
    @8
    cP
    @15
    cprime
    @8
    cP
    @7
    @15
    @8
    id
    c4
    c3
    @6
    c9
    c3
    @14
    3nn0
    4nn0
    3nn0
    @14
    eqid
    9nn0
    4t3e12
    3t3e9
    decmul1
    syl6eqr
    eleq1d
    mtbiri
    pm2.21d
    @9
    @0
    ax-1
    3jaoi
    com12
    3ad2ant1
    mpd
end
