include "cst.mm"
include "wcel.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "c3.mm"
include "wceq.mm"
include "c1.mm"
include "cch.mm"
include "cr.mm"
include "stcl.mm"
include "mpi.mm"
include "recnd.mm"
include "addassd.mm"
include "eqeq1d.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "eqcom.mm"
include "wne.mm"
include "wi.mm"
include "readdcld.mm"
include "ltne.mm"
include "ex.mm"
include "syl.mm"
include "necon2bd.mm"
include "syl5bi.mm"
include "wa.mm"
include "cle.mm"
include "1re.mm"
include "readdcli.mm"
include "a1i.mm"
include "1red.mm"
include "stle1.mm"
include "le2addd.mm"
include "leadd2dd.mm"
include "adantr.mm"
include "w3a.mm"
include "ltadd1.mm"
include "biimpd.mm"
include "syl3anc.mm"
include "imp.mm"
include "readdcl.mm"
include "sylancl.mm"
include "lelttr.mm"
include "mp2and.mm"
include "c2.mm"
include "df-3.mm"
include "df-2.mm"
include "oveq1i.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "3eqtrri.mm"
include "syl6breq.mm"
include "con3d.mm"
include "wo.mm"
include "wb.mm"
include "leloe.mm"
include "mpbid.mm"
include "ord.mm"
include "3syld.mm"
include "sylbid.mm"

theorem stadd3i
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  assume stle.1: |- A e. CH
  assume stle.2: |- B e. CH
  assume stm1add3.3: |- C e. CH


  assert |- ( S e. States -> ( ( ( ( S ` A ) + ( S ` B ) ) + ( S ` C ) ) = 3 -> ( S ` A ) = 1 ) )

  proof
    cS
    cst
    wcel
    #
    cA
    cS
    cfv
    #
    cB
    cS
    cfv
    #
    caddc
    co
    cC
    cS
    cfv
    #
    caddc
    co
    #
    c3
    wceq
    @1
    @2
    @3
    caddc
    co
    #
    caddc
    co
    #
    c3
    wceq
    #
    @1
    c1
    wceq
    #
    @0
    @4
    @6
    c3
    @0
    @1
    @2
    @3
    @0
    @1
    @0
    cA
    cch
    wcel
    #
    @1
    cr
    wcel
    #
    stle.1
    cA
    cS
    stcl
    mpi
    #
    recnd
    @0
    @2
    @0
    cB
    cch
    wcel
    #
    @2
    cr
    wcel
    stle.2
    cB
    cS
    stcl
    mpi
    #
    recnd
    @0
    @3
    @0
    cC
    cch
    wcel
    #
    @3
    cr
    wcel
    stm1add3.3
    cC
    cS
    stcl
    mpi
    #
    recnd
    addassd
    eqeq1d
    @0
    @7
    @6
    c3
    clt
    wbr
    #
    wn
    #
    @1
    c1
    clt
    wbr
    #
    wn
    @8
    @7
    c3
    @6
    wceq
    @0
    @17
    @6
    c3
    eqcom
    @0
    @16
    c3
    @6
    @0
    @6
    cr
    wcel
    #
    @16
    c3
    @6
    wne
    #
    wi
    @0
    @1
    @5
    @11
    @0
    @2
    @3
    @13
    @15
    readdcld
    #
    readdcld
    #
    @19
    @16
    @20
    @6
    c3
    ltne
    ex
    syl
    necon2bd
    syl5bi
    @0
    @18
    @16
    @0
    @18
    @16
    @0
    @18
    wa
    #
    @6
    c1
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    c3
    clt
    @23
    @6
    @1
    @24
    caddc
    co
    #
    cle
    wbr
    #
    @26
    @25
    clt
    wbr
    #
    @6
    @25
    clt
    wbr
    #
    @0
    @27
    @18
    @0
    @5
    @24
    @1
    @21
    @24
    cr
    wcel
    #
    @0
    c1
    c1
    1re
    1re
    readdcli
    #
    a1i
    #
    @11
    @0
    @2
    @3
    c1
    c1
    @13
    @15
    @0
    1red
    #
    @33
    @0
    @12
    @2
    c1
    cle
    wbr
    stle.2
    cB
    cS
    stle1
    mpi
    @0
    @14
    @3
    c1
    cle
    wbr
    stm1add3.3
    cC
    cS
    stle1
    mpi
    le2addd
    leadd2dd
    adantr
    @0
    @18
    @28
    @0
    @10
    c1
    cr
    wcel
    #
    @30
    @18
    @28
    wi
    @11
    @33
    @32
    @10
    @34
    @30
    w3a
    @18
    @28
    @1
    c1
    @24
    ltadd1
    biimpd
    syl3anc
    imp
    @0
    @27
    @28
    wa
    @29
    wi
    #
    @18
    @0
    @19
    @26
    cr
    wcel
    #
    @25
    cr
    wcel
    #
    @35
    @22
    @0
    @10
    @30
    @36
    @11
    @31
    @1
    @24
    readdcl
    sylancl
    @37
    @0
    c1
    @24
    1re
    @31
    readdcli
    a1i
    @6
    @26
    @25
    lelttr
    syl3anc
    adantr
    mp2and
    c3
    c2
    c1
    caddc
    co
    @24
    c1
    caddc
    co
    @25
    df-3
    c2
    @24
    c1
    caddc
    df-2
    oveq1i
    c1
    c1
    c1
    ax-1cn
    ax-1cn
    ax-1cn
    addassi
    3eqtrri
    syl6breq
    ex
    con3d
    @0
    @18
    @8
    @0
    @1
    c1
    cle
    wbr
    #
    @18
    @8
    wo
    #
    @0
    @9
    @38
    stle.1
    cA
    cS
    stle1
    mpi
    @0
    @10
    @34
    @38
    @39
    wb
    @11
    1re
    @1
    c1
    leloe
    sylancl
    mpbid
    ord
    3syld
    sylbid
end
