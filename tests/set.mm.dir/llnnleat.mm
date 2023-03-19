include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "ccvr.mm"
include "cfv.mm"
include "wbr.mm"
include "wrex.mm"
include "wn.mm"
include "cbs.mm"
include "wa.mm"
include "simp2.mm"
include "wb.mm"
include "eqid.mm"
include "islln.mm"
include "3ad2ant1.mm"
include "mpbid.mm"
include "simprd.mm"
include "cplt.mm"
include "cal.mm"
include "simp11.mm"
include "hlatl.mm"
include "syl.mm"
include "simp13.mm"
include "atnlt.mm"
include "syl3anc.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "simp12.mm"
include "llnbase.mm"
include "simp3.mm"
include "cvrlt.mm"
include "syl31anc.mm"
include "cpo.mm"
include "wi.mm"
include "hlpos.mm"
include "pltletr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "mtod.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem llnnleat
  let cA: class A
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let vq: setvar q
  assume llnnleat.l: |- .<_ = ( le ` K )
  assume llnnleat.a: |- A = ( Atoms ` K )
  assume llnnleat.n: |- N = ( LLines ` K )


  assert |- ( ( K e. HL /\ X e. N /\ P e. A ) -> -. X .<_ P )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    #
    vq
    cv
    #
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    vq
    cA
    wrex
    #
    cX
    cP
    c.le
    wbr
    #
    wn
    #
    @3
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @3
    @1
    @11
    @7
    wa
    #
    @0
    @1
    @2
    simp2
    @0
    @1
    @1
    @12
    wb
    @2
    cA
    @10
    @5
    chlt
    cK
    cN
    cX
    vq
    @10
    eqid
    #
    @5
    eqid
    #
    llnnleat.a
    llnnleat.n
    islln
    3ad2ant1
    mpbid
    simprd
    @3
    @6
    @9
    vq
    cA
    @3
    @4
    cA
    wcel
    #
    @6
    w3a
    #
    @8
    @4
    cP
    cK
    cplt
    cfv
    #
    wbr
    #
    @16
    cK
    cal
    wcel
    #
    @15
    @2
    @18
    wn
    @16
    @0
    @19
    @0
    @1
    @2
    @15
    @6
    simp11
    #
    cK
    hlatl
    syl
    @3
    @15
    @6
    simp2
    @0
    @1
    @2
    @15
    @6
    simp13
    #
    cA
    @4
    cP
    @17
    cK
    @17
    eqid
    #
    llnnleat.a
    atnlt
    syl3anc
    @16
    @4
    cX
    @17
    wbr
    #
    @8
    @18
    @16
    @0
    @4
    @10
    wcel
    #
    @11
    @6
    @23
    @20
    @15
    @3
    @24
    @6
    cA
    @10
    @4
    cK
    @13
    llnnleat.a
    atbase
    3ad2ant2
    #
    @16
    @1
    @11
    @0
    @1
    @2
    @15
    @6
    simp12
    @10
    cK
    cN
    cX
    @13
    llnnleat.n
    llnbase
    syl
    #
    @3
    @15
    @6
    simp3
    chlt
    @10
    @5
    @17
    cK
    @4
    cX
    @13
    @22
    @14
    cvrlt
    syl31anc
    @16
    cK
    cpo
    wcel
    #
    @24
    @11
    cP
    @10
    wcel
    #
    @23
    @8
    wa
    @18
    wi
    @16
    @0
    @27
    @20
    cK
    hlpos
    syl
    @25
    @26
    @16
    @2
    @28
    @21
    cA
    @10
    cP
    cK
    @13
    llnnleat.a
    atbase
    syl
    @10
    @17
    cK
    c.le
    @4
    cX
    cP
    @13
    llnnleat.l
    @22
    pltletr
    syl13anc
    mpand
    mtod
    rexlimdv3a
    mpd
end
