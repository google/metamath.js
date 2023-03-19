include "cdm.mm"
include "crn.mm"
include "cin.mm"
include "ccnv.mm"
include "c0.mm"
include "wceq.mm"
include "df-rn.mm"
include "ineq2i.mm"
include "a1i.mm"
include "dmeqd.mm"
include "ineq2d.mm"
include "dm0.mm"
include "in0.mm"
include "eqtri.mm"
include "3eqtrd.mm"
include "coemptyd.mm"

theorem conrel2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume conrel1d.a: |- ( ph -> `' A = (/) )


  assert |- ( ph -> ( B o. A ) = (/) )

  proof
    wph
    cB
    cA
    wph
    cB
    cdm
    #
    cA
    crn
    #
    cin
    #
    @0
    cA
    ccnv
    #
    cdm
    #
    cin
    #
    @0
    c0
    cdm
    #
    cin
    #
    c0
    @2
    @5
    wceq
    wph
    @1
    @4
    @0
    cA
    df-rn
    ineq2i
    a1i
    wph
    @4
    @6
    @0
    wph
    @3
    c0
    conrel1d.a
    dmeqd
    ineq2d
    @7
    c0
    wceq
    wph
    @7
    @0
    c0
    cin
    c0
    @6
    c0
    @0
    dm0
    ineq2i
    @0
    in0
    eqtri
    a1i
    3eqtrd
    coemptyd
end
