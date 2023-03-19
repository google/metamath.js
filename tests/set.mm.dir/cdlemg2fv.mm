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
include "cdlemg2fvlem.mm"

theorem cdlemg2fv
  let cA: class A
  let cB: class B
  let cP: class P
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cQ: class Q
  assume cdlemg2inv.h: |- H = ( LHyp ` K )
  assume cdlemg2inv.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg2j.l: |- .<_ = ( le ` K )
  assume cdlemg2j.j: |- .\/ = ( join ` K )
  assume cdlemg2j.a: |- A = ( Atoms ` K )
  assume cdlemg2j.m: |- ./\ = ( meet ` K )
  assume cdlemg2j.b: |- B = ( Base ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( X e. B /\ -. X .<_ W ) ) /\ ( F e. T /\ ( P .\/ ( X ./\ W ) ) = X ) ) -> ( F ` X ) = ( ( F ` P ) .\/ ( X ./\ W ) ) )

  proof
    vx
    vy
    vz
    vt
    cA
    cB
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
    @2
    @1
    @0
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
    cT
    @4
    @3
    @5
    vs
    cv
    #
    @0
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
    cB
    @1
    @2
    wne
    vx
    cv
    #
    cW
    c.le
    wbr
    wn
    wa
    @6
    cW
    c.le
    wbr
    wn
    @6
    @8
    cW
    c.an
    co
    #
    c.or
    co
    @8
    wceq
    wa
    vz
    cv
    @6
    @3
    c.le
    wbr
    @0
    cW
    c.le
    wbr
    wn
    @0
    @3
    c.le
    wbr
    wn
    wa
    vy
    cv
    @7
    wceq
    wi
    vt
    cA
    wral
    vy
    cB
    crio
    vt
    @6
    @5
    csb
    cif
    @9
    c.or
    co
    wceq
    wi
    vs
    cA
    wral
    vz
    cB
    crio
    @8
    cif
    cmpt
    #
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    vs
    vq
    vp
    cdlemg2j.b
    cdlemg2j.l
    cdlemg2j.j
    cdlemg2j.m
    cdlemg2j.a
    cdlemg2inv.h
    cdlemg2inv.t
    @4
    eqid
    @5
    eqid
    @7
    eqid
    @10
    eqid
    cdlemg2fvlem
end
