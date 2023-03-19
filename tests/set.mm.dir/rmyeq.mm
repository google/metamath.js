include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wceq.mm"
include "crmy.mm"
include "co.mm"
include "wb.mm"
include "cv.mm"
include "oveq2.mm"
include "zssre.mm"
include "wa.mm"
include "frmy.mm"
include "fovcl.mm"
include "zred.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "ltrmy.mm"
include "biimpd.mm"
include "3expb.mm"
include "eqord1.mm"
include "3impb.mm"

theorem rmyeq
  let cA: class A
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( M = N <-> ( A rmY M ) = ( A rmY N ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cM
    cz
    wcel
    cN
    cz
    wcel
    cM
    cN
    wceq
    cA
    cM
    crmy
    co
    #
    cA
    cN
    crmy
    co
    #
    wceq
    wb
    @1
    va
    vb
    cA
    va
    cv
    #
    crmy
    co
    #
    cA
    vb
    cv
    #
    crmy
    co
    #
    cM
    cN
    cz
    @2
    @3
    @4
    @6
    cA
    crmy
    oveq2
    @4
    cM
    cA
    crmy
    oveq2
    @4
    cN
    cA
    crmy
    oveq2
    zssre
    @1
    @4
    cz
    wcel
    #
    wa
    @5
    cA
    @4
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    @1
    @8
    @6
    cz
    wcel
    #
    @4
    @6
    clt
    wbr
    #
    @5
    @7
    clt
    wbr
    #
    wi
    @1
    @8
    @9
    w3a
    @10
    @11
    cA
    @4
    @6
    ltrmy
    biimpd
    3expb
    eqord1
    3impb
end
