include "cn.mm"
include "wcel.mm"
include "c6.mm"
include "c4.mm"
include "cdc.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "clt.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "wa.mm"
include "cprime.mm"
include "wrex.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "wi.mm"
include "elnnuz.mm"
include "ax-1.mm"
include "c3.mm"
include "c5.mm"
include "cc0.mm"
include "c7.mm"
include "c8.mm"
include "wn.mm"
include "cr.mm"
include "6nn0.mm"
include "4nn0.mm"
include "deccl.mm"
include "nn0rei.mm"
include "a1i.mm"
include "8nn0.mm"
include "3nn0.mm"
include "eluzelre.mm"
include "4lt10.mm"
include "6lt8.mm"
include "decltc.mm"
include "eluzle.mm"
include "ltletrd.mm"
include "wb.mm"
include "ltnle.mm"
include "sylancr.mm"
include "mpbid.mm"
include "pm2.21d.mm"
include "83prm.mm"
include "2nn0.mm"
include "eqid.mm"
include "4t2e8.mm"
include "3t2e6.mm"
include "decmul1.mm"
include "3lt10.mm"
include "4lt8.mm"
include "wceq.mm"
include "6nn.mm"
include "3lt6.mm"
include "declt.mm"
include "orci.mm"
include "bpos1lem.mm"
include "43prm.mm"
include "2t2e4.mm"
include "2lt4.mm"
include "23prm.mm"
include "1nn0.mm"
include "2cn.mm"
include "mulid2i.mm"
include "1lt2.mm"
include "13prm.mm"
include "7nn0.mm"
include "7t2e14.mm"
include "1nn.mm"
include "7lt10.mm"
include "declti.mm"
include "4nn.mm"
include "3lt4.mm"
include "7prm.mm"
include "5nn0.mm"
include "5t2e10.mm"
include "5lt7.mm"
include "5prm.mm"
include "3lt5.mm"
include "5lt6.mm"
include "3prm.mm"
include "2lt3.mm"
include "2prm.mm"
include "olci.mm"
include "sylbi.mm"
include "imp.mm"

theorem bpos1
  let cN: class N
  let vp: setvar p

  disjoint N p
  assert |- ( ( N e. NN /\ N <_ ; 6 4 ) -> E. p e. Prime ( N < p /\ p <_ ( 2 x. N ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c6
    c4
    cdc
    #
    cle
    wbr
    #
    cN
    vp
    cv
    #
    clt
    wbr
    @3
    c2
    cN
    cmul
    co
    cle
    wbr
    wa
    vp
    cprime
    wrex
    #
    @0
    cN
    c1
    cuz
    cfv
    wcel
    @2
    @4
    wi
    #
    cN
    elnnuz
    @5
    c1
    c2
    c2
    cN
    vp
    @4
    @2
    ax-1
    #
    @5
    c2
    c4
    c3
    cN
    vp
    @6
    @5
    c3
    c6
    c5
    cN
    vp
    @6
    @5
    c5
    c1
    cc0
    cdc
    #
    c7
    cN
    vp
    @6
    @5
    c7
    c1
    c4
    cdc
    #
    c1
    c3
    cdc
    #
    cN
    vp
    @6
    @5
    @9
    c2
    c6
    cdc
    #
    c2
    c3
    cdc
    #
    cN
    vp
    @6
    @5
    @11
    c4
    c6
    cdc
    #
    c4
    c3
    cdc
    #
    cN
    vp
    @6
    @5
    @13
    c8
    c6
    cdc
    #
    c8
    c3
    cdc
    #
    cN
    vp
    @6
    cN
    @15
    cuz
    cfv
    wcel
    #
    @2
    @4
    @16
    @1
    cN
    clt
    wbr
    #
    @2
    wn
    #
    @16
    @1
    @15
    cN
    @1
    cr
    wcel
    #
    @16
    @1
    c6
    c4
    6nn0
    4nn0
    deccl
    nn0rei
    #
    a1i
    @15
    cr
    wcel
    @16
    @15
    c8
    c3
    8nn0
    3nn0
    deccl
    nn0rei
    a1i
    @15
    cN
    eluzelre
    #
    @1
    @15
    clt
    wbr
    @16
    c6
    c8
    c4
    c3
    6nn0
    8nn0
    4nn0
    3nn0
    4lt10
    6lt8
    decltc
    a1i
    @15
    cN
    eluzle
    ltletrd
    @16
    @19
    cN
    cr
    wcel
    @17
    @18
    wb
    @20
    @21
    @1
    cN
    ltnle
    sylancr
    mpbid
    pm2.21d
    83prm
    c4
    c3
    4nn0
    3nn0
    deccl
    c4
    c3
    c8
    c6
    c2
    @13
    2nn0
    4nn0
    3nn0
    @13
    eqid
    6nn0
    4t2e8
    3t2e6
    decmul1
    c4
    c8
    c3
    c3
    4nn0
    8nn0
    3nn0
    3nn0
    3lt10
    4lt8
    decltc
    @15
    @14
    clt
    wbr
    @15
    @14
    wceq
    c8
    c3
    c6
    8nn0
    3nn0
    6nn
    3lt6
    declt
    orci
    bpos1lem
    43prm
    c2
    c3
    2nn0
    3nn0
    deccl
    c2
    c3
    c4
    c6
    c2
    @11
    2nn0
    2nn0
    3nn0
    @11
    eqid
    6nn0
    2t2e4
    3t2e6
    decmul1
    c2
    c4
    c3
    c3
    2nn0
    4nn0
    3nn0
    3nn0
    3lt10
    2lt4
    decltc
    @13
    @12
    clt
    wbr
    @13
    @12
    wceq
    c4
    c3
    c6
    4nn0
    3nn0
    6nn
    3lt6
    declt
    orci
    bpos1lem
    23prm
    c1
    c3
    1nn0
    3nn0
    deccl
    c1
    c3
    c2
    c6
    c2
    @9
    2nn0
    1nn0
    3nn0
    @9
    eqid
    6nn0
    c2
    2cn
    mulid2i
    #
    3t2e6
    decmul1
    c1
    c2
    c3
    c3
    1nn0
    2nn0
    3nn0
    3nn0
    3lt10
    1lt2
    decltc
    @11
    @10
    clt
    wbr
    @11
    @10
    wceq
    c2
    c3
    c6
    2nn0
    3nn0
    6nn
    3lt6
    declt
    orci
    bpos1lem
    13prm
    7nn0
    7t2e14
    c1
    c3
    c7
    1nn
    3nn0
    7nn0
    7lt10
    declti
    @9
    @8
    clt
    wbr
    @9
    @8
    wceq
    c1
    c3
    c4
    1nn0
    3nn0
    4nn
    3lt4
    declt
    orci
    bpos1lem
    7prm
    5nn0
    5t2e10
    5lt7
    c7
    @7
    clt
    wbr
    c7
    @7
    wceq
    7lt10
    orci
    bpos1lem
    5prm
    3nn0
    3t2e6
    3lt5
    c5
    c6
    clt
    wbr
    c5
    c6
    wceq
    5lt6
    orci
    bpos1lem
    3prm
    2nn0
    2t2e4
    2lt3
    c3
    c4
    clt
    wbr
    c3
    c4
    wceq
    3lt4
    orci
    bpos1lem
    2prm
    1nn0
    @22
    1lt2
    c2
    c2
    wceq
    c2
    c2
    clt
    wbr
    c2
    eqid
    olci
    bpos1lem
    sylbi
    imp
end
