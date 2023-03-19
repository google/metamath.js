include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
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
include "cdlemg2klem.mm"

theorem cdlemg2k
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cX: class X
  assume cdlemg2inv.h: |- H = ( LHyp ` K )
  assume cdlemg2inv.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg2j.l: |- .<_ = ( le ` K )
  assume cdlemg2j.j: |- .\/ = ( join ` K )
  assume cdlemg2j.a: |- A = ( Atoms ` K )
  assume cdlemg2j.m: |- ./\ = ( meet ` K )
  assume cdlemg2j.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ F e. T ) -> ( ( F ` P ) .\/ ( F ` Q ) ) = ( ( F ` P ) .\/ U ) )

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
    c.an
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
    c.an
    co
    c.or
    co
    c.an
    co
    #
    cP
    cQ
    cT
    @5
    @4
    @6
    vs
    cv
    #
    @1
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
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
    @7
    cW
    c.le
    wbr
    wn
    @7
    @9
    cW
    c.an
    co
    #
    c.or
    co
    @9
    wceq
    wa
    vz
    cv
    @7
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
    @8
    wceq
    wi
    vt
    cA
    wral
    vy
    @0
    crio
    vt
    @7
    @6
    csb
    cif
    @10
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
    @9
    cif
    cmpt
    #
    cH
    c.or
    cK
    c.le
    c.an
    cU
    cW
    vs
    vq
    vp
    @0
    eqid
    cdlemg2j.l
    cdlemg2j.j
    cdlemg2j.m
    cdlemg2j.a
    cdlemg2inv.h
    cdlemg2inv.t
    @5
    eqid
    @6
    eqid
    @8
    eqid
    @11
    eqid
    cdlemg2j.u
    cdlemg2klem
end
