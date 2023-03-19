include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2.mm"
include "simp3l.mm"
include "cdleme4.mm"
include "syl131anc.mm"
include "simp3r.mm"
include "cdleme2.mm"
include "syl13anc.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "simp11l.mm"
include "simp2l.mm"
include "simp3rl.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "oveq12d.mm"

theorem cdleme39a
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme39.l: |- .<_ = ( le ` K )
  assume cdleme39.j: |- .\/ = ( join ` K )
  assume cdleme39.m: |- ./\ = ( meet ` K )
  assume cdleme39.a: |- A = ( Atoms ` K )
  assume cdleme39.h: |- H = ( LHyp ` K )
  assume cdleme39.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme39.e: |- E = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme39.g: |- G = ( ( P .\/ Q ) ./\ ( E .\/ ( ( R .\/ t ) ./\ W ) ) )
  assume cdleme39a.v: |- V = ( ( t .\/ E ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ P e. A /\ Q e. A ) /\ ( R e. A /\ -. R .<_ W ) /\ ( R .<_ ( P .\/ Q ) /\ ( t e. A /\ -. t .<_ W ) ) ) -> G = ( ( R .\/ V ) ./\ ( E .\/ ( ( t .\/ R ) ./\ W ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    vt
    cv
    #
    cA
    wcel
    #
    @11
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    w3a
    #
    cG
    @9
    cE
    cR
    @11
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cR
    cV
    c.or
    co
    #
    cE
    @11
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cdleme39.g
    @16
    @9
    @20
    @19
    @23
    c.an
    @16
    @9
    cR
    cU
    c.or
    co
    #
    @20
    @16
    @2
    @3
    @4
    @8
    @10
    @9
    @24
    wceq
    @2
    @3
    @4
    @8
    @15
    simp11
    #
    @2
    @3
    @4
    @8
    @15
    simp12
    #
    @2
    @3
    @4
    @8
    @15
    simp13
    #
    @5
    @8
    @15
    simp2
    @5
    @8
    @10
    @14
    simp3l
    cA
    cP
    cQ
    cR
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme39.l
    cdleme39.j
    cdleme39.m
    cdleme39.a
    cdleme39.h
    cdleme39.u
    cdleme4
    syl131anc
    @16
    cV
    cU
    cR
    c.or
    @16
    cV
    @11
    cE
    c.or
    co
    cW
    c.an
    co
    #
    cU
    cdleme39a.v
    @16
    @2
    @3
    @4
    @14
    @28
    cU
    wceq
    @25
    @26
    @27
    @5
    @8
    @10
    @14
    simp3r
    cA
    cP
    cQ
    @11
    cU
    cE
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme39.l
    cdleme39.j
    cdleme39.m
    cdleme39.a
    cdleme39.h
    cdleme39.u
    cdleme39.e
    cdleme2
    syl13anc
    syl5eq
    oveq2d
    eqtr4d
    @16
    @18
    @22
    cE
    c.or
    @16
    @17
    @21
    cW
    c.an
    @16
    @0
    @6
    @12
    @17
    @21
    wceq
    @0
    @1
    @3
    @4
    @8
    @15
    simp11l
    @5
    @6
    @7
    @15
    simp2l
    @12
    @13
    @10
    @5
    @8
    simp3rl
    cA
    c.or
    cK
    cR
    @11
    cdleme39.j
    cdleme39.a
    hlatjcom
    syl3anc
    oveq1d
    oveq2d
    oveq12d
    syl5eq
end
