include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cpr.mm"
include "csn.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "prprc1.mm"
include "wi.mm"
include "c1.mm"
include "hashsng.mm"
include "wa.mm"
include "fveq2.mm"
include "eqcomd.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "id.mm"
include "wne.mm"
include "1ne2.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "syl.mm"
include "expcom.mm"
include "c0.mm"
include "snprc.mm"
include "cc0.mm"
include "eqeq2.mm"
include "hash0.mm"
include "0ne2.mm"
include "sylancl.mm"
include "ex.mm"
include "sylbi.mm"
include "pm2.61i.mm"

theorem elprchashprn2
  let cM: class M
  let cN: class N


  assert |- ( -. M e. _V -> -. ( # ` { M , N } ) = 2 )

  proof
    cM
    cvv
    wcel
    wn
    cM
    cN
    cpr
    #
    cN
    csn
    #
    wceq
    #
    @0
    chash
    cfv
    #
    c2
    wceq
    wn
    #
    cM
    cN
    prprc1
    cN
    cvv
    wcel
    #
    @2
    @4
    wi
    #
    @5
    @1
    chash
    cfv
    #
    c1
    wceq
    #
    @6
    cN
    cvv
    hashsng
    @2
    @8
    @4
    @2
    @8
    wa
    @3
    c1
    wceq
    #
    @4
    @2
    @8
    @9
    @2
    @7
    @3
    c1
    @2
    @3
    @7
    @0
    @1
    chash
    fveq2
    eqcomd
    eqeq1d
    biimpa
    @9
    @3
    c2
    @9
    @3
    c1
    c2
    @9
    id
    c1
    c2
    wne
    @9
    1ne2
    a1i
    eqnetrd
    neneqd
    syl
    expcom
    syl
    @5
    wn
    @1
    c0
    wceq
    #
    @6
    cN
    snprc
    @10
    @2
    @4
    @10
    @2
    wa
    @0
    c0
    wceq
    #
    c0
    chash
    cfv
    #
    cc0
    wceq
    #
    @4
    @10
    @2
    @11
    @1
    c0
    @0
    eqeq2
    biimpa
    hash0
    @11
    @13
    wa
    @3
    cc0
    wceq
    #
    @4
    @11
    @13
    @14
    @11
    @12
    @3
    cc0
    @11
    @3
    @12
    @0
    c0
    chash
    fveq2
    eqcomd
    eqeq1d
    biimpa
    @14
    @3
    c2
    @14
    @3
    cc0
    c2
    @14
    id
    cc0
    c2
    wne
    @14
    0ne2
    a1i
    eqnetrd
    neneqd
    syl
    sylancl
    ex
    sylbi
    pm2.61i
    syl
end
