include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cneg.mm"
include "wne.mm"
include "catan.mm"
include "cdm.mm"
include "simpl.mm"
include "sqcl.mm"
include "adantr.mm"
include "abscld.mm"
include "cn0.mm"
include "wceq.mm"
include "2nn0.mm"
include "absexp.mm"
include "sylancl.mm"
include "simpr.mm"
include "cr.mm"
include "abscl.mm"
include "1red.mm"
include "cc0.mm"
include "cle.mm"
include "absge0.mm"
include "0le1.mm"
include "a1i.mm"
include "lt2sqd.mm"
include "mpbid.mm"
include "sq1.mm"
include "syl6breq.mm"
include "eqbrtrd.mm"
include "ltned.mm"
include "fveq2.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "syl.mm"
include "atandm3.mm"
include "sylanbrc.mm"

theorem bndatandm
  let cA: class A


  assert |- ( ( A e. CC /\ ( abs ` A ) < 1 ) -> A e. dom arctan )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wa
    #
    @0
    cA
    c2
    cexp
    co
    #
    c1
    cneg
    #
    wne
    #
    cA
    catan
    cdm
    wcel
    @0
    @2
    simpl
    #
    @3
    @4
    cabs
    cfv
    #
    c1
    wne
    @6
    @3
    @8
    c1
    @3
    @4
    @0
    @4
    cc
    wcel
    @2
    cA
    sqcl
    adantr
    abscld
    @3
    @8
    @1
    c2
    cexp
    co
    #
    c1
    clt
    @3
    @0
    c2
    cn0
    wcel
    @8
    @9
    wceq
    @7
    2nn0
    cA
    c2
    absexp
    sylancl
    @3
    @9
    c1
    c2
    cexp
    co
    #
    c1
    clt
    @3
    @2
    @9
    @10
    clt
    wbr
    @0
    @2
    simpr
    @3
    @1
    c1
    @0
    @1
    cr
    wcel
    @2
    cA
    abscl
    adantr
    @3
    1red
    @0
    cc0
    @1
    cle
    wbr
    @2
    cA
    absge0
    adantr
    cc0
    c1
    cle
    wbr
    @3
    0le1
    a1i
    lt2sqd
    mpbid
    sq1
    syl6breq
    eqbrtrd
    ltned
    @4
    @5
    @8
    c1
    @4
    @5
    wceq
    @8
    @5
    cabs
    cfv
    #
    c1
    @4
    @5
    cabs
    fveq2
    @11
    c1
    cabs
    cfv
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    syl6eq
    necon3i
    syl
    cA
    atandm3
    sylanbrc
end
