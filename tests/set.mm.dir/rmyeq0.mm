include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "crmy.mm"
include "co.mm"
include "wb.mm"
include "0z.mm"
include "cv.mm"
include "oveq2.mm"
include "zssre.mm"
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
include "mpanr2.mm"
include "rmy0.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "bitrd.mm"

theorem rmyeq0
  let cA: class A
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( N = 0 <-> ( A rmY N ) = 0 ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cN
    cc0
    wceq
    #
    cA
    cN
    crmy
    co
    #
    cA
    cc0
    crmy
    co
    #
    wceq
    #
    @5
    cc0
    wceq
    @1
    @2
    cc0
    cz
    wcel
    @4
    @7
    wb
    0z
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
    cN
    cc0
    cz
    @5
    @6
    @8
    @10
    cA
    crmy
    oveq2
    @8
    cN
    cA
    crmy
    oveq2
    @8
    cc0
    cA
    crmy
    oveq2
    zssre
    @1
    @8
    cz
    wcel
    #
    wa
    @9
    cA
    @8
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    @1
    @12
    @10
    cz
    wcel
    #
    @8
    @10
    clt
    wbr
    #
    @9
    @11
    clt
    wbr
    #
    wi
    @1
    @12
    @13
    w3a
    @14
    @15
    cA
    @8
    @10
    ltrmy
    biimpd
    3expb
    eqord1
    mpanr2
    @3
    @6
    cc0
    @5
    @1
    @6
    cc0
    wceq
    @2
    cA
    rmy0
    adantr
    eqeq2d
    bitrd
end
