include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "catm.mm"
include "cfv.mm"
include "wne.mm"
include "wex.mm"
include "c0.mm"
include "eqid.mm"
include "atex.mm"
include "n0.mm"
include "sylib.mm"
include "adantr.mm"
include "cple.mm"
include "wbr.mm"
include "wn.mm"
include "llnnleat.mm"
include "3expa.mm"
include "wceq.mm"
include "cops.mm"
include "cbs.mm"
include "hlop.mm"
include "ad2antrr.mm"
include "atbase.mm"
include "adantl.mm"
include "op0le.mm"
include "syl2anc.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "exlimddv.mm"

theorem llnn0
  let cK: class K
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vp: setvar p
  assume llnn0.z: |- .0. = ( 0. ` K )
  assume llnn0.n: |- N = ( LLines ` K )


  assert |- ( ( K e. HL /\ X e. N ) -> X =/= .0. )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    wa
    #
    vp
    cv
    #
    cK
    catm
    cfv
    #
    wcel
    #
    cX
    c.0
    wne
    #
    vp
    @0
    @5
    vp
    wex
    #
    @1
    @0
    @4
    c0
    wne
    @7
    @4
    cK
    @4
    eqid
    #
    atex
    vp
    @4
    n0
    sylib
    adantr
    @2
    @5
    wa
    #
    cX
    @3
    cK
    cple
    cfv
    #
    wbr
    #
    wn
    #
    @6
    @0
    @1
    @5
    @12
    @4
    @3
    cK
    @10
    cN
    cX
    @10
    eqid
    #
    @8
    llnn0.n
    llnnleat
    3expa
    @9
    @11
    cX
    c.0
    @9
    @11
    cX
    c.0
    wceq
    c.0
    @3
    @10
    wbr
    #
    @9
    cK
    cops
    wcel
    #
    @3
    cK
    cbs
    cfv
    #
    wcel
    #
    @14
    @0
    @15
    @1
    @5
    cK
    hlop
    ad2antrr
    @5
    @17
    @2
    @4
    @16
    @3
    cK
    @16
    eqid
    #
    @8
    atbase
    adantl
    @16
    cK
    @10
    @3
    c.0
    @18
    @13
    llnn0.z
    op0le
    syl2anc
    cX
    c.0
    @3
    @10
    breq1
    syl5ibrcom
    necon3bd
    mpd
    exlimddv
end
