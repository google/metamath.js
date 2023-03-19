include "chil.mm"
include "wss.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "wa.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "ocel.mm"
include "simplbda.mm"
include "adantl.mm"
include "wi.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "ad2antlr.mm"
include "wb.mm"
include "ssel2.mm"
include "ocss.mm"
include "sselda.mm"
include "orthcom.mm"
include "syl2an.mm"
include "sylibrd.mm"
include "mpd.mm"
include "anandis.mm"
include "ex.mm"

theorem ocorth
  let cA: class A
  let cB: class B
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( H C_ ~H -> ( ( A e. H /\ B e. ( _|_ ` H ) ) -> ( A .ih B ) = 0 ) )

  proof
    cH
    chil
    wss
    #
    cA
    cH
    wcel
    #
    cB
    cH
    cort
    cfv
    #
    wcel
    #
    wa
    cA
    cB
    csp
    co
    cc0
    wceq
    #
    @0
    @1
    @3
    @4
    @0
    @1
    wa
    #
    @0
    @3
    wa
    #
    wa
    #
    cB
    vx
    cv
    #
    csp
    co
    #
    cc0
    wceq
    #
    vx
    cH
    wral
    #
    @4
    @6
    @11
    @5
    @0
    @3
    cB
    chil
    wcel
    #
    @11
    vx
    cB
    cH
    ocel
    simplbda
    adantl
    @7
    @11
    cB
    cA
    csp
    co
    #
    cc0
    wceq
    #
    @4
    @1
    @11
    @14
    wi
    @0
    @6
    @10
    @14
    vx
    cA
    cH
    @8
    cA
    wceq
    @9
    @13
    cc0
    @8
    cA
    cB
    csp
    oveq2
    eqeq1d
    rspcv
    ad2antlr
    @5
    cA
    chil
    wcel
    @12
    @4
    @14
    wb
    @6
    cH
    chil
    cA
    ssel2
    @0
    @2
    chil
    cB
    cH
    ocss
    sselda
    cA
    cB
    orthcom
    syl2an
    sylibrd
    mpd
    anandis
    ex
end
