include "wcel.mm"
include "cfn.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "wb.mm"
include "wn.mm"
include "wa.mm"
include "cr.mm"
include "cpnf.mm"
include "pnfnre.mm"
include "neli.mm"
include "hashinf.mm"
include "eleq1d.mm"
include "mtbiri.mm"
include "id.mm"
include "0re.mm"
include "syl6eqel.mm"
include "nsyl.mm"
include "0fin.mm"
include "con3i.mm"
include "adantl.mm"
include "2falsed.mm"
include "ex.mm"
include "cen.mm"
include "wbr.mm"
include "hashen.mm"
include "mpan2.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "fz10.mm"
include "fveq2i.mm"
include "cn0.mm"
include "0nn0.mm"
include "hashfz1.mm"
include "ax-mp.mm"
include "eqtr3i.mm"
include "eqeq2i.mm"
include "en0.mm"
include "3bitr3g.mm"
include "pm2.61d2.mm"

theorem hasheq0
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( ( # ` A ) = 0 <-> A = (/) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cfn
    wcel
    #
    cA
    chash
    cfv
    #
    cc0
    wceq
    #
    cA
    c0
    wceq
    #
    wb
    #
    @0
    @1
    wn
    #
    @5
    @0
    @6
    wa
    #
    @3
    @4
    @7
    @2
    cr
    wcel
    #
    @3
    @7
    @8
    cpnf
    cr
    wcel
    cpnf
    cr
    pnfnre
    neli
    @7
    @2
    cpnf
    cr
    cA
    cV
    hashinf
    eleq1d
    mtbiri
    @3
    @2
    cc0
    cr
    @3
    id
    0re
    syl6eqel
    nsyl
    @6
    @4
    wn
    @0
    @4
    @1
    @4
    cA
    c0
    cfn
    @4
    id
    0fin
    syl6eqel
    con3i
    adantl
    2falsed
    ex
    @1
    @2
    c0
    chash
    cfv
    #
    wceq
    #
    cA
    c0
    cen
    wbr
    #
    @3
    @4
    @1
    c0
    cfn
    wcel
    @10
    @11
    wb
    0fin
    cA
    c0
    hashen
    mpan2
    @9
    cc0
    @2
    c1
    cc0
    cfz
    co
    #
    chash
    cfv
    #
    @9
    cc0
    @12
    c0
    chash
    fz10
    fveq2i
    cc0
    cn0
    wcel
    @13
    cc0
    wceq
    0nn0
    cc0
    hashfz1
    ax-mp
    eqtr3i
    eqeq2i
    cA
    en0
    3bitr3g
    pm2.61d2
end
