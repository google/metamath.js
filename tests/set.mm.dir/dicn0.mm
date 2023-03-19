include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "cltrn.mm"
include "cmpt.mm"
include "cop.mm"
include "c0.mm"
include "wne.mm"
include "coc.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "ctendo.mm"
include "simpl.mm"
include "eqid.mm"
include "lhpocnel.mm"
include "adantr.mm"
include "simpr.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "tendo02.mm"
include "syl.mm"
include "eqcomd.mm"
include "tendo0cl.mm"
include "cvv.mm"
include "fvex.mm"
include "resiexg.mm"
include "ax-mp.mm"
include "mptex.mm"
include "dicopelval.mm"
include "mpbir2and.mm"
include "ne0i.mm"

theorem dicn0
  let cA: class A
  let cQ: class Q
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vg: setvar g
  let vf: setvar f
  assume dicn0.l: |- .<_ = ( le ` K )
  assume dicn0.a: |- A = ( Atoms ` K )
  assume dicn0.h: |- H = ( LHyp ` K )
  assume dicn0.i: |- I = ( ( DIsoC ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( I ` Q ) =/= (/) )

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
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    #
    cid
    cK
    cbs
    cfv
    #
    cres
    #
    vf
    cW
    cK
    cltrn
    cfv
    #
    cfv
    #
    @4
    cmpt
    #
    cop
    #
    cQ
    cI
    cfv
    #
    wcel
    #
    @9
    c0
    wne
    @2
    @10
    @4
    cW
    cK
    coc
    cfv
    #
    cfv
    #
    vg
    cv
    cfv
    cQ
    wceq
    vg
    @6
    crio
    #
    @7
    cfv
    #
    wceq
    @7
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    #
    @2
    @14
    @4
    @2
    @13
    @6
    wcel
    #
    @14
    @4
    wceq
    @2
    @0
    @12
    cA
    wcel
    @12
    cW
    c.le
    wbr
    wn
    wa
    #
    @1
    @17
    @0
    @1
    simpl
    @0
    @18
    @1
    cA
    cH
    cK
    c.le
    @11
    cW
    dicn0.l
    @11
    eqid
    dicn0.a
    dicn0.h
    lhpocnel
    adantr
    @0
    @1
    simpr
    cA
    @12
    cQ
    @6
    vg
    @13
    cH
    cK
    c.le
    cW
    dicn0.l
    dicn0.a
    dicn0.h
    @6
    eqid
    #
    @13
    eqid
    ltrniotacl
    syl3anc
    @3
    @6
    vf
    @13
    cK
    @7
    @7
    eqid
    #
    @3
    eqid
    #
    tendo02
    syl
    eqcomd
    @0
    @16
    @1
    @3
    @6
    vf
    @15
    cH
    cK
    @7
    cW
    @21
    dicn0.h
    @19
    @15
    eqid
    #
    @20
    tendo0cl
    adantr
    cA
    @12
    cQ
    @7
    @6
    vg
    @15
    @4
    cH
    cI
    cK
    c.le
    chlt
    cW
    dicn0.l
    dicn0.a
    dicn0.h
    @12
    eqid
    @19
    @22
    dicn0.i
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    cK
    cbs
    fvex
    @3
    cvv
    resiexg
    ax-mp
    vf
    @6
    @4
    cW
    @5
    fvex
    mptex
    dicopelval
    mpbir2and
    @9
    @8
    ne0i
    syl
end
