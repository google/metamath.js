include "wcel.mm"
include "cz.mm"
include "cabs.mm"
include "cfv.mm"
include "cprime.mm"
include "zring.mm"
include "zringbas.mm"
include "irredcl.mm"
include "cn0.mm"
include "wb.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elnn0.mm"
include "ax-1.mm"
include "crg.mm"
include "wne.mm"
include "zringring.mm"
include "zring0.mm"
include "irredn0.mm"
include "mpan.mm"
include "necon2bi.mm"
include "pm2.21d.mm"
include "jaoi.mm"
include "sylbi.mm"
include "prmnn.mm"
include "a1i.mm"
include "prmirredlem.mm"
include "pm5.21ndd.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "absidd.mm"
include "eleq1d.mm"
include "bitr4d.mm"
include "adantl.mm"
include "cminusg.mm"
include "eqid.mm"
include "irrednegb.mm"
include "ccnfld.mm"
include "csubg.mm"
include "csubrg.mm"
include "zsubrg.mm"
include "subrgsubg.mm"
include "ax-mp.mm"
include "df-zring.mm"
include "subginv.mm"
include "cc.mm"
include "zcn.mm"
include "cnfldneg.mm"
include "syl.mm"
include "eqtr3d.mm"
include "bitrd.mm"
include "adantr.mm"
include "zre.mm"
include "cle.mm"
include "wbr.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "le0neg1d.mm"
include "mpbird.mm"
include "absnidd.mm"
include "3bitr4d.mm"
include "adantrl.mm"
include "elznn0nn.mm"
include "biimpi.mm"
include "mpjaodan.mm"
include "biadan2.mm"

theorem prmirred
  let cA: class A
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  assume prmirred.i: |- I = ( Irred ` ZZring )


  assert |- ( A e. I <-> ( A e. ZZ /\ ( abs ` A ) e. Prime ) )

  proof
    cA
    cI
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cabs
    cfv
    #
    cprime
    wcel
    #
    cz
    zring
    cI
    cA
    prmirred.i
    zringbas
    irredcl
    @1
    cA
    cn0
    wcel
    #
    @0
    @3
    wb
    #
    cA
    cr
    wcel
    #
    cA
    cneg
    #
    cn
    wcel
    #
    wa
    #
    @4
    @5
    @1
    @4
    @0
    cA
    cprime
    wcel
    #
    @3
    @4
    cA
    cn
    wcel
    #
    @0
    @10
    @4
    @11
    cA
    cc0
    wceq
    #
    wo
    @0
    @11
    wi
    #
    cA
    elnn0
    @11
    @13
    @12
    @11
    @0
    ax-1
    @12
    @0
    @11
    @0
    cA
    cc0
    zring
    crg
    wcel
    #
    @0
    cA
    cc0
    wne
    zringring
    zring
    cI
    cA
    cc0
    prmirred.i
    zring0
    irredn0
    mpan
    necon2bi
    pm2.21d
    jaoi
    sylbi
    @10
    @11
    wi
    @4
    cA
    prmnn
    a1i
    @11
    @0
    @10
    wb
    wi
    @4
    cA
    cI
    prmirred.i
    prmirredlem
    a1i
    pm5.21ndd
    @4
    @2
    cA
    cprime
    @4
    cA
    cA
    nn0re
    cA
    nn0ge0
    absidd
    eleq1d
    bitr4d
    adantl
    @1
    @8
    @5
    @6
    @1
    @8
    wa
    #
    @7
    cI
    wcel
    #
    @7
    cprime
    wcel
    #
    @0
    @3
    @8
    @16
    @17
    wb
    @1
    @7
    cI
    prmirred.i
    prmirredlem
    adantl
    @1
    @0
    @16
    wb
    @8
    @1
    @0
    cA
    zring
    cminusg
    cfv
    #
    cfv
    #
    cI
    wcel
    #
    @16
    @14
    @1
    @0
    @20
    wb
    zringring
    cz
    zring
    cI
    @18
    cA
    prmirred.i
    @18
    eqid
    #
    zringbas
    irrednegb
    mpan
    @1
    @19
    @7
    cI
    @1
    cA
    ccnfld
    cminusg
    cfv
    #
    cfv
    #
    @19
    @7
    cz
    ccnfld
    csubg
    cfv
    wcel
    #
    @1
    @23
    @19
    wceq
    cz
    ccnfld
    csubrg
    cfv
    wcel
    @24
    zsubrg
    cz
    ccnfld
    subrgsubg
    ax-mp
    cz
    ccnfld
    zring
    @22
    @18
    cA
    df-zring
    @22
    eqid
    @21
    subginv
    mpan
    @1
    cA
    cc
    wcel
    @23
    @7
    wceq
    cA
    zcn
    cA
    cnfldneg
    syl
    eqtr3d
    eleq1d
    bitrd
    adantr
    @15
    @2
    @7
    cprime
    @15
    cA
    @1
    @6
    @8
    cA
    zre
    adantr
    #
    @15
    cA
    cc0
    cle
    wbr
    cc0
    @7
    cle
    wbr
    #
    @8
    @26
    @1
    @8
    @7
    @7
    nnnn0
    nn0ge0d
    adantl
    @15
    cA
    @25
    le0neg1d
    mpbird
    absnidd
    eleq1d
    3bitr4d
    adantrl
    @1
    @4
    @9
    wo
    cA
    elznn0nn
    biimpi
    mpjaodan
    biadan2
end
