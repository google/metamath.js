include "cz.mm"
include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "ccoe.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "c0p.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "fveq2.mm"
include "coe0.mm"
include "a1i.mm"
include "eqtrd.mm"
include "fveq1d.mm"
include "adantl.mm"
include "id.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "syl.mm"
include "adantr.mm"
include "3ad2antl2.mm"
include "wn.mm"
include "neneq.mm"
include "3ad2antl3.mm"
include "pm2.65da.mm"
include "neqned.mm"

theorem n0p
  let cP: class P
  let cN: class N


  assert |- ( ( P e. ( Poly ` ZZ ) /\ N e. NN0 /\ ( ( coeff ` P ) ` N ) =/= 0 ) -> P =/= 0p )

  proof
    cP
    cz
    cply
    cfv
    wcel
    #
    cN
    cn0
    wcel
    #
    cN
    cP
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wne
    #
    w3a
    #
    cP
    c0p
    @5
    cP
    c0p
    wceq
    #
    @3
    cc0
    wceq
    #
    @1
    @0
    @6
    @7
    @4
    @1
    @6
    wa
    @3
    cN
    cn0
    cc0
    csn
    cxp
    #
    cfv
    #
    cc0
    @6
    @3
    @9
    wceq
    @1
    @6
    cN
    @2
    @8
    @6
    @2
    c0p
    ccoe
    cfv
    #
    @8
    cP
    c0p
    ccoe
    fveq2
    @10
    @8
    wceq
    @6
    coe0
    a1i
    eqtrd
    fveq1d
    adantl
    @1
    @9
    cc0
    wceq
    #
    @6
    @1
    @1
    @11
    @1
    id
    cn0
    cc0
    cN
    c0ex
    fvconst2
    syl
    adantr
    eqtrd
    3ad2antl2
    @4
    @0
    @6
    @7
    wn
    #
    @1
    @4
    @12
    @6
    @3
    cc0
    neneq
    adantr
    3ad2antl3
    pm2.65da
    neqned
end
