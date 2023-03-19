include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cn.mm"
include "cc0.mm"
include "wi.mm"
include "elnn0.mm"
include "cle.mm"
include "wa.mm"
include "elnnnn0c.mm"
include "1red.mm"
include "nn0re.mm"
include "leloed.mm"
include "cz.mm"
include "wb.mm"
include "1zzd.mm"
include "nn0z.mm"
include "zltp1le.mm"
include "syl2anc.mm"
include "1p1e2.mm"
include "breq1i.mm"
include "a1i.mm"
include "cr.mm"
include "2re.mm"
include "3bitrd.mm"
include "olc.mm"
include "2a1d.mm"
include "c3.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqcoms.mm"
include "adantl.mm"
include "2p1e3.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "wn.mm"
include "3halfnz.mm"
include "pm2.24d.mm"
include "mpi.mm"
include "syl6bi.mm"
include "expcom.mm"
include "jaoi.mm"
include "com12.mm"
include "sylbid.mm"
include "orc.mm"
include "imp.mm"
include "sylbi.mm"
include "0p1e1.mm"
include "halfnz.mm"

theorem nn0o1gt2
  let cN: class N


  assert |- ( ( N e. NN0 /\ ( ( N + 1 ) / 2 ) e. NN0 ) -> ( N = 1 \/ 2 < N ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    cN
    c1
    wceq
    #
    c2
    cN
    clt
    wbr
    #
    wo
    #
    @0
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @3
    @6
    wi
    #
    cN
    elnn0
    @7
    @9
    @8
    @7
    @0
    c1
    cN
    cle
    wbr
    #
    wa
    @9
    cN
    elnnnn0c
    @0
    @10
    @9
    @0
    @10
    c1
    cN
    clt
    wbr
    #
    c1
    cN
    wceq
    #
    wo
    #
    @9
    @0
    c1
    cN
    @0
    1red
    cN
    nn0re
    #
    leloed
    @13
    @0
    @9
    @11
    @0
    @9
    wi
    #
    @12
    @0
    @11
    @9
    @0
    @11
    @5
    c2
    cN
    wceq
    #
    wo
    #
    @9
    @0
    @11
    c1
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    c2
    cN
    cle
    wbr
    #
    @17
    @0
    c1
    cz
    wcel
    cN
    cz
    wcel
    @11
    @19
    wb
    @0
    1zzd
    cN
    nn0z
    c1
    cN
    zltp1le
    syl2anc
    @19
    @20
    wb
    @0
    @18
    c2
    cN
    cle
    1p1e2
    breq1i
    a1i
    @0
    c2
    cN
    c2
    cr
    wcel
    @0
    2re
    a1i
    @14
    leloed
    3bitrd
    @17
    @0
    @9
    @5
    @15
    @16
    @5
    @6
    @0
    @3
    @5
    @4
    olc
    2a1d
    @0
    @16
    @9
    @0
    @16
    wa
    #
    @3
    c3
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    @6
    @21
    @2
    @22
    cn0
    @21
    @2
    c2
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @22
    @16
    @2
    @25
    wceq
    #
    @0
    @26
    cN
    c2
    cN
    c2
    wceq
    @1
    @24
    c2
    cdiv
    cN
    c2
    c1
    caddc
    oveq1
    oveq1d
    eqcoms
    adantl
    @24
    c3
    c2
    cdiv
    2p1e3
    oveq1i
    syl6eq
    eleq1d
    @23
    @22
    cz
    wcel
    #
    wn
    @6
    3halfnz
    @23
    @27
    @6
    @22
    nn0z
    pm2.24d
    mpi
    syl6bi
    expcom
    jaoi
    com12
    sylbid
    com12
    @12
    @6
    @0
    @3
    @6
    cN
    c1
    @4
    @5
    orc
    eqcoms
    2a1d
    jaoi
    com12
    sylbid
    imp
    sylbi
    @8
    @3
    c1
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    @6
    @8
    @2
    @28
    cn0
    @8
    @1
    c1
    c2
    cdiv
    @8
    @1
    cc0
    c1
    caddc
    co
    c1
    cN
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    oveq1d
    eleq1d
    @29
    @28
    cz
    wcel
    #
    wn
    @6
    halfnz
    @29
    @30
    @6
    @28
    nn0z
    pm2.24d
    mpi
    syl6bi
    jaoi
    sylbi
    imp
end
