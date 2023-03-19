include "cn0.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "w3o.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "cr.mm"
include "nn0re.mm"
include "lttri4.mm"
include "syl2an.mm"
include "3adant3.mm"
include "wi.mm"
include "cz.mm"
include "fmtnonn.mm"
include "nnzd.mm"
include "gcdcom.mm"
include "syl2anr.mm"
include "goldbachthlem2.mm"
include "eqtrd.mm"
include "3exp.mm"
include "impcom.mm"
include "eqneqall.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "3expia.mm"
include "3jaod.mm"
include "mpd.mm"

theorem goldbachth
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ M e. NN0 /\ N =/= M ) -> ( ( FermatNo ` N ) gcd ( FermatNo ` M ) ) = 1 )

  proof
    cN
    cn0
    wcel
    #
    cM
    cn0
    wcel
    #
    cN
    cM
    wne
    #
    w3a
    #
    cN
    cM
    clt
    wbr
    #
    cN
    cM
    wceq
    #
    cM
    cN
    clt
    wbr
    #
    w3o
    #
    cN
    cfmtno
    cfv
    #
    cM
    cfmtno
    cfv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    @0
    @1
    @7
    @2
    @0
    cN
    cr
    wcel
    cM
    cr
    wcel
    @7
    @1
    cN
    nn0re
    cM
    nn0re
    cN
    cM
    lttri4
    syl2an
    3adant3
    @3
    @4
    @11
    @5
    @6
    @0
    @1
    @4
    @11
    wi
    #
    @2
    @1
    @0
    @12
    @1
    @0
    @4
    @11
    @1
    @0
    @4
    w3a
    @10
    @9
    @8
    cgcd
    co
    #
    c1
    @1
    @0
    @10
    @13
    wceq
    #
    @4
    @0
    @8
    cz
    wcel
    @9
    cz
    wcel
    @14
    @1
    @0
    @8
    cN
    fmtnonn
    nnzd
    @1
    @9
    cM
    fmtnonn
    nnzd
    @8
    @9
    gcdcom
    syl2anr
    3adant3
    cN
    cM
    goldbachthlem2
    eqtrd
    3exp
    impcom
    3adant3
    @2
    @0
    @5
    @11
    wi
    @1
    @5
    @2
    @11
    @11
    cN
    cM
    eqneqall
    com12
    3ad2ant3
    @0
    @1
    @6
    @11
    wi
    @2
    @0
    @1
    @6
    @11
    cM
    cN
    goldbachthlem2
    3expia
    3adant3
    3jaod
    mpd
end
