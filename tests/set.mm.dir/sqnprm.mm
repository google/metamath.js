include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cprime.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "zre.mm"
include "adantr.mm"
include "absresq.mm"
include "syl.mm"
include "recnd.mm"
include "abscld.mm"
include "sqvald.mm"
include "eqtr3d.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "cuz.mm"
include "wn.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "nn0abscl.mm"
include "nn0zd.mm"
include "sq1.mm"
include "prmuz2.mm"
include "adantl.mm"
include "eluz2b1.mm"
include "simprbi.mm"
include "breqtrrd.mm"
include "syl5eqbr.mm"
include "cc0.mm"
include "cle.mm"
include "wb.mm"
include "absge0d.mm"
include "1re.mm"
include "0le1.mm"
include "lt2sq.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "sylanbrc.mm"
include "nprm.mm"
include "pm2.65da.mm"

theorem sqnprm
  let cA: class A


  assert |- ( A e. ZZ -> -. ( A ^ 2 ) e. Prime )

  proof
    cA
    cz
    wcel
    #
    cA
    c2
    cexp
    co
    #
    cprime
    wcel
    #
    cA
    cabs
    cfv
    #
    @3
    cmul
    co
    #
    cprime
    wcel
    #
    @0
    @2
    wa
    #
    @1
    @4
    cprime
    @6
    @3
    c2
    cexp
    co
    #
    @1
    @4
    @6
    cA
    cr
    wcel
    #
    @7
    @1
    wceq
    @0
    @8
    @2
    cA
    zre
    adantr
    #
    cA
    absresq
    syl
    #
    @6
    @3
    @6
    @3
    @6
    cA
    @6
    cA
    @9
    recnd
    #
    abscld
    #
    recnd
    sqvald
    eqtr3d
    @0
    @2
    simpr
    eqeltrrd
    @6
    @3
    c2
    cuz
    cfv
    #
    wcel
    #
    @14
    @5
    wn
    @6
    @3
    cz
    wcel
    c1
    @3
    clt
    wbr
    #
    @14
    @6
    @3
    @0
    @3
    cn0
    wcel
    @2
    cA
    nn0abscl
    adantr
    nn0zd
    @6
    @15
    c1
    c2
    cexp
    co
    #
    @7
    clt
    wbr
    #
    @6
    @16
    c1
    @7
    clt
    sq1
    @6
    c1
    @1
    @7
    clt
    @6
    @1
    @13
    wcel
    #
    c1
    @1
    clt
    wbr
    #
    @2
    @18
    @0
    @1
    prmuz2
    adantl
    @18
    @1
    cz
    wcel
    @19
    @1
    eluz2b1
    simprbi
    syl
    @10
    breqtrrd
    syl5eqbr
    @6
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @15
    @17
    wb
    #
    @12
    @6
    cA
    @11
    absge0d
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @20
    @21
    wa
    @22
    1re
    0le1
    c1
    @3
    lt2sq
    mpanl12
    syl2anc
    mpbird
    @3
    eluz2b1
    sylanbrc
    #
    @23
    @3
    @3
    nprm
    syl2anc
    pm2.65da
end
