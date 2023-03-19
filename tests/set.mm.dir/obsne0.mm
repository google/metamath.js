include "cobs.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "csca.mm"
include "cur.mm"
include "c0g.mm"
include "wne.mm"
include "cdr.mm"
include "cphl.mm"
include "clvec.mm"
include "obsrcl.mm"
include "phllvec.mm"
include "eqid.mm"
include "lvecdrng.mm"
include "3syl.mm"
include "adantr.mm"
include "drngunz.mm"
include "syl.mm"
include "cip.mm"
include "co.mm"
include "wceq.mm"
include "obsipid.mm"
include "eqeq1d.mm"
include "cbs.mm"
include "wb.mm"
include "obsss.mm"
include "sselda.mm"
include "ipeq0.mm"
include "syl2anc.mm"
include "bitr3d.mm"
include "necon3bid.mm"
include "mpbid.mm"

theorem obsne0
  let cA: class A
  let cB: class B
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume obsocv.z: |- .0. = ( 0g ` W )


  assert |- ( ( B e. ( OBasis ` W ) /\ A e. B ) -> A =/= .0. )

  proof
    cB
    cW
    cobs
    cfv
    wcel
    #
    cA
    cB
    wcel
    #
    wa
    #
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    @3
    c0g
    cfv
    #
    wne
    #
    cA
    c.0
    wne
    @2
    @3
    cdr
    wcel
    #
    @6
    @0
    @7
    @1
    @0
    cW
    cphl
    wcel
    #
    cW
    clvec
    wcel
    @7
    cB
    cW
    obsrcl
    #
    cW
    phllvec
    @3
    cW
    @3
    eqid
    #
    lvecdrng
    3syl
    adantr
    @3
    @4
    @5
    @5
    eqid
    #
    @4
    eqid
    #
    drngunz
    syl
    @2
    @4
    @5
    cA
    c.0
    @2
    cA
    cA
    cW
    cip
    cfv
    #
    co
    #
    @5
    wceq
    #
    @4
    @5
    wceq
    cA
    c.0
    wceq
    #
    @2
    @14
    @4
    @5
    cA
    cB
    @4
    @3
    @13
    cW
    @13
    eqid
    #
    @10
    @12
    obsipid
    eqeq1d
    @2
    @8
    cA
    cW
    cbs
    cfv
    #
    wcel
    @15
    @16
    wb
    @0
    @8
    @1
    @9
    adantr
    @0
    cB
    @18
    cA
    cB
    @18
    cW
    @18
    eqid
    #
    obsss
    sselda
    cA
    @3
    @13
    @18
    cW
    c.0
    @5
    @10
    @17
    @19
    @11
    obsocv.z
    ipeq0
    syl2anc
    bitr3d
    necon3bid
    mpbid
end
