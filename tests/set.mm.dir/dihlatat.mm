include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "c0g.mm"
include "cdif.mm"
include "wrex.mm"
include "ccnv.mm"
include "clvec.mm"
include "wb.mm"
include "id.mm"
include "dvhlvec.mm"
include "eqid.mm"
include "islsat.mm"
include "syl.mm"
include "biimpa.mm"
include "wi.mm"
include "wne.mm"
include "eldifsn.mm"
include "dihlspsnat.mm"
include "3expb.mm"
include "sylan2b.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "adantr.mm"
include "mpd.mm"

theorem dihlatat
  let cA: class A
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cW: class W
  let vv: setvar v
  assume dihlatat.a: |- A = ( Atoms ` K )
  assume dihlatat.h: |- H = ( LHyp ` K )
  assume dihlatat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihlatat.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihlatat.l: |- L = ( LSAtoms ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ Q e. L ) -> ( `' I ` Q ) e. A )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cL
    wcel
    #
    wa
    cQ
    vv
    cv
    #
    csn
    cU
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    vv
    cU
    cbs
    cfv
    #
    cU
    c0g
    cfv
    #
    csn
    cdif
    #
    wrex
    #
    cQ
    cI
    ccnv
    #
    cfv
    #
    cA
    wcel
    #
    @0
    @1
    @9
    @0
    cU
    clvec
    wcel
    @1
    @9
    wb
    @0
    cU
    cH
    cK
    cW
    dihlatat.h
    dihlatat.u
    @0
    id
    dvhlvec
    vv
    cL
    cQ
    @3
    @6
    cU
    clvec
    @7
    @6
    eqid
    #
    @3
    eqid
    #
    @7
    eqid
    #
    dihlatat.l
    islsat
    syl
    biimpa
    @0
    @9
    @12
    wi
    @1
    @0
    @5
    @12
    vv
    @8
    @0
    @2
    @8
    wcel
    #
    wa
    @12
    @5
    @4
    @10
    cfv
    #
    cA
    wcel
    #
    @16
    @0
    @2
    @6
    wcel
    #
    @2
    @7
    wne
    #
    wa
    @18
    @2
    @6
    @7
    eldifsn
    @0
    @19
    @20
    @18
    cA
    cU
    cH
    cI
    cK
    @3
    @6
    cW
    @2
    @7
    dihlatat.a
    dihlatat.h
    dihlatat.u
    @13
    @15
    @14
    dihlatat.i
    dihlspsnat
    3expb
    sylan2b
    @5
    @11
    @17
    cA
    cQ
    @4
    @10
    fveq2
    eleq1d
    syl5ibrcom
    rexlimdva
    adantr
    mpd
end
