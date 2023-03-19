include "wcel.mm"
include "wa.mm"
include "cwlkson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cwlks.mm"
include "cc0.mm"
include "wceq.mm"
include "chash.mm"
include "w3a.mm"
include "wb.mm"
include "cv.mm"
include "wlkson.mm"
include "fveq1.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "simpr.mm"
include "fveq2.mm"
include "adantr.mm"
include "fveq12d.mm"
include "2rbropap.mm"
include "3expb.mm"

theorem iswlkon
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assume wlkson.v: |- V = ( Vtx ` G )


  assert |- ( ( ( A e. V /\ B e. V ) /\ ( F e. U /\ P e. Z ) ) -> ( F ( A ( WalksOn ` G ) B ) P <-> ( F ( Walks ` G ) P /\ ( P ` 0 ) = A /\ ( P ` ( # ` F ) ) = B ) ) )

  proof
    cA
    cV
    wcel
    cB
    cV
    wcel
    wa
    #
    cF
    cU
    wcel
    cP
    cZ
    wcel
    cF
    cP
    cA
    cB
    cG
    cwlkson
    cfv
    co
    #
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    #
    wbr
    cc0
    cP
    cfv
    #
    cA
    wceq
    #
    cF
    chash
    cfv
    #
    cP
    cfv
    #
    cB
    wceq
    #
    w3a
    wb
    @0
    cc0
    vp
    cv
    #
    cfv
    #
    cA
    wceq
    @4
    @7
    vf
    cv
    #
    chash
    cfv
    #
    @8
    cfv
    #
    cB
    wceq
    cP
    vf
    cF
    @1
    @2
    cU
    cZ
    vp
    cA
    cB
    vf
    cG
    cV
    vp
    wlkson.v
    wlkson
    @10
    cF
    wceq
    #
    @8
    cP
    wceq
    #
    wa
    #
    @9
    @3
    cA
    @14
    @9
    @3
    wceq
    @13
    cc0
    @8
    cP
    fveq1
    adantl
    eqeq1d
    @15
    @12
    @6
    cB
    @15
    @11
    @5
    @8
    cP
    @13
    @14
    simpr
    @13
    @11
    @5
    wceq
    @14
    @10
    cF
    chash
    fveq2
    adantr
    fveq12d
    eqeq1d
    2rbropap
    3expb
end
