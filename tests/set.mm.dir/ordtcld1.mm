include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cordt.mm"
include "cfv.mm"
include "ccld.mm"
include "cuni.mm"
include "wss.mm"
include "cdif.mm"
include "ssrab2.mm"
include "ctopon.mm"
include "wceq.mm"
include "ordttopon.mm"
include "adantr.mm"
include "toponuni.mm"
include "syl.mm"
include "syl5sseq.mm"
include "wn.mm"
include "notrab.mm"
include "difeq1d.mm"
include "syl5eqr.mm"
include "ordtopn1.mm"
include "eqeltrrd.mm"
include "ctop.mm"
include "wb.mm"
include "topontop.mm"
include "eqid.mm"
include "iscld.mm"
include "3syl.mm"
include "mpbir2and.mm"

theorem ordtcld1
  let vx: setvar x
  let cP: class P
  let cR: class R
  let cV: class V
  let cX: class X
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume ordttopon.3: |- X = dom R

  disjoint P x
  disjoint R x
  disjoint V x
  disjoint X x
  disjoint A x
  disjoint B x
  disjoint x y
  disjoint P y
  disjoint R y
  disjoint V y
  disjoint X y
  assert |- ( ( R e. V /\ P e. X ) -> { x e. X | x R P } e. ( Clsd ` ( ordTop ` R ) ) )

  proof
    cR
    cV
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    vx
    cv
    cP
    cR
    wbr
    #
    vx
    cX
    crab
    #
    cR
    cordt
    cfv
    #
    ccld
    cfv
    wcel
    #
    @4
    @5
    cuni
    #
    wss
    #
    @7
    @4
    cdif
    #
    @5
    wcel
    #
    @2
    cX
    @4
    @7
    @3
    vx
    cX
    ssrab2
    @2
    @5
    cX
    ctopon
    cfv
    wcel
    #
    cX
    @7
    wceq
    @0
    @11
    @1
    cR
    cV
    cX
    ordttopon.3
    ordttopon
    adantr
    #
    cX
    @5
    toponuni
    syl
    #
    syl5sseq
    @2
    @3
    wn
    vx
    cX
    crab
    #
    @9
    @5
    @2
    @14
    cX
    @4
    cdif
    @9
    @3
    vx
    cX
    notrab
    @2
    cX
    @7
    @4
    @13
    difeq1d
    syl5eqr
    vx
    cP
    cR
    cV
    cX
    ordttopon.3
    ordtopn1
    eqeltrrd
    @2
    @11
    @5
    ctop
    wcel
    @6
    @8
    @10
    wa
    wb
    @12
    cX
    @5
    topontop
    @4
    @5
    @7
    @7
    eqid
    iscld
    3syl
    mpbir2and
end
