include "crg.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "ply1sclf.mm"
include "wa.mm"
include "cc0.mm"
include "cco1.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "ply1sclid.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem ply1sclf1
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let c.0: class .0.
  assume ply1scl.p: |- P = ( Poly1 ` R )
  assume ply1scl.a: |- A = ( algSc ` P )
  assume ply1sclid.k: |- K = ( Base ` R )
  assume ply1sclf1.b: |- B = ( Base ` P )


  assert |- ( R e. Ring -> A : K -1-1-> B )

  proof
    cR
    crg
    wcel
    #
    cK
    cB
    cA
    wf
    vx
    cv
    #
    cA
    cfv
    #
    vy
    cv
    #
    cA
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cK
    wral
    vx
    cK
    wral
    cK
    cB
    cA
    wf1
    cA
    cB
    cP
    cR
    cK
    ply1scl.p
    ply1scl.a
    ply1sclid.k
    ply1sclf1.b
    ply1sclf
    @0
    @7
    vx
    vy
    cK
    cK
    @5
    @6
    @0
    @1
    cK
    wcel
    #
    @3
    cK
    wcel
    #
    wa
    wa
    #
    cc0
    @2
    cco1
    cfv
    #
    cfv
    #
    cc0
    @4
    cco1
    cfv
    #
    cfv
    #
    wceq
    @5
    cc0
    @11
    @13
    @2
    @4
    cco1
    fveq2
    fveq1d
    @10
    @1
    @12
    @3
    @14
    @0
    @8
    @1
    @12
    wceq
    @9
    cA
    cP
    cR
    cK
    @1
    ply1scl.p
    ply1scl.a
    ply1sclid.k
    ply1sclid
    adantrr
    @0
    @9
    @3
    @14
    wceq
    @8
    cA
    cP
    cR
    cK
    @3
    ply1scl.p
    ply1scl.a
    ply1sclid.k
    ply1sclid
    adantrl
    eqeq12d
    syl5ibr
    ralrimivva
    vx
    vy
    cK
    cB
    cA
    dff13
    sylanbrc
end
