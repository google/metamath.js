include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmee.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "csb.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "cdlemg2jlemOLDN.mm"

theorem cdlemg2jOLDN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cdlemg2inv.h: |- H = ( LHyp ` K )
  assume cdlemg2inv.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg2j.l: |- .<_ = ( le ` K )
  assume cdlemg2j.j: |- .\/ = ( join ` K )
  assume cdlemg2j.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ F e. T ) -> ( F ` ( P .\/ Q ) ) = ( ( F ` P ) .\/ ( F ` Q ) ) )

  proof
    vx
    vy
    vz
    vt
    cA
    cK
    cbs
    cfv
    #
    vt
    cv
    #
    vp
    cv
    #
    vq
    cv
    #
    c.or
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    c.or
    co
    @3
    @2
    @1
    c.or
    co
    cW
    @5
    co
    c.or
    co
    @5
    co
    #
    cP
    cQ
    cT
    @6
    @4
    @7
    vs
    cv
    #
    @1
    c.or
    co
    cW
    @5
    co
    c.or
    co
    @5
    co
    #
    cF
    vx
    @0
    @2
    @3
    wne
    vx
    cv
    #
    cW
    c.le
    wbr
    wn
    wa
    @8
    cW
    c.le
    wbr
    wn
    @8
    @10
    cW
    @5
    co
    #
    c.or
    co
    @10
    wceq
    wa
    vz
    cv
    @8
    @4
    c.le
    wbr
    @1
    cW
    c.le
    wbr
    wn
    @1
    @4
    c.le
    wbr
    wn
    wa
    vy
    cv
    @9
    wceq
    wi
    vt
    cA
    wral
    vy
    @0
    crio
    vt
    @8
    @7
    csb
    cif
    @11
    c.or
    co
    wceq
    wi
    vs
    cA
    wral
    vz
    @0
    crio
    @10
    cif
    cmpt
    #
    cH
    c.or
    cK
    c.le
    @5
    cW
    vs
    vq
    vp
    @0
    eqid
    cdlemg2j.l
    cdlemg2j.j
    @5
    eqid
    cdlemg2j.a
    cdlemg2inv.h
    cdlemg2inv.t
    @6
    eqid
    @7
    eqid
    @9
    eqid
    @12
    eqid
    cdlemg2jlemOLDN
end
