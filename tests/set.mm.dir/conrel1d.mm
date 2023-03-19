include "cdm.mm"
include "crn.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "wceq.mm"
include "ccnv.mm"
include "dfdm4.mm"
include "rneqd.mm"
include "rn0.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "ineq2.mm"
include "in0.mm"
include "syl.mm"
include "coemptyd.mm"

theorem conrel1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume conrel1d.a: |- ( ph -> `' A = (/) )


  assert |- ( ph -> ( A o. B ) = (/) )

  proof
    wph
    cA
    cB
    wph
    cA
    cdm
    #
    cB
    crn
    #
    cin
    @1
    @0
    cin
    #
    c0
    @0
    @1
    incom
    wph
    @0
    c0
    wceq
    #
    @2
    c0
    wceq
    wph
    @0
    cA
    ccnv
    #
    crn
    #
    c0
    cA
    dfdm4
    wph
    @5
    c0
    crn
    c0
    wph
    @4
    c0
    conrel1d.a
    rneqd
    rn0
    syl6eq
    syl5eq
    @3
    @2
    @1
    c0
    cin
    c0
    @0
    c0
    @1
    ineq2
    @1
    in0
    syl6eq
    syl
    syl5eq
    coemptyd
end
