include "cst.mm"
include "wcel.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "c1.mm"
include "wne.mm"
include "cr.mm"
include "cch.mm"
include "stcl.mm"
include "mpi.mm"
include "readdcld.mm"
include "wa.mm"
include "ltne.mm"
include "necomd.mm"
include "sylan.mm"
include "ex.mm"
include "necon2bd.mm"
include "cle.mm"
include "1re.mm"
include "a1i.mm"
include "stle1.mm"
include "leadd2dd.mm"
include "adantr.mm"
include "wi.mm"
include "w3a.mm"
include "ltadd1.mm"
include "biimpd.mm"
include "syl3anc.mm"
include "imp.mm"
include "readdcl.mm"
include "sylancl.mm"
include "readdcli.mm"
include "lelttr.mm"
include "mp2and.mm"
include "df-2.mm"
include "syl6breqr.mm"
include "con3d.mm"
include "wo.mm"
include "wb.mm"
include "leloe.mm"
include "mpbid.mm"
include "ord.mm"
include "3syld.mm"

theorem staddi
  let cA: class A
  let cB: class B
  let cS: class S
  assume stle.1: |- A e. CH
  assume stle.2: |- B e. CH


  assert |- ( S e. States -> ( ( ( S ` A ) + ( S ` B ) ) = 2 -> ( S ` A ) = 1 ) )

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
    #
    c2
    wceq
    @3
    c2
    clt
    wbr
    #
    wn
    @1
    c1
    clt
    wbr
    #
    wn
    @1
    c1
    wceq
    #
    @0
    @4
    @3
    c2
    @0
    @4
    @3
    c2
    wne
    #
    @0
    @3
    cr
    wcel
    #
    @4
    @7
    @0
    @1
    @2
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
    readdcld
    #
    @8
    @4
    wa
    c2
    @3
    @3
    c2
    ltne
    necomd
    sylan
    ex
    necon2bd
    @0
    @5
    @4
    @0
    @5
    @4
    @0
    @5
    wa
    #
    @3
    c1
    c1
    caddc
    co
    #
    c2
    clt
    @15
    @3
    @1
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @17
    @16
    clt
    wbr
    #
    @3
    @16
    clt
    wbr
    #
    @0
    @18
    @5
    @0
    @2
    c1
    @1
    @13
    c1
    cr
    wcel
    #
    @0
    1re
    a1i
    #
    @11
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
    leadd2dd
    adantr
    @0
    @5
    @19
    @0
    @10
    @21
    @21
    @5
    @19
    wi
    @11
    @22
    @22
    @10
    @21
    @21
    w3a
    @5
    @19
    @1
    c1
    c1
    ltadd1
    biimpd
    syl3anc
    imp
    @0
    @18
    @19
    wa
    @20
    wi
    #
    @5
    @0
    @8
    @17
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    @23
    @14
    @0
    @10
    @21
    @24
    @11
    1re
    @1
    c1
    readdcl
    sylancl
    @25
    @0
    c1
    c1
    1re
    1re
    readdcli
    a1i
    @3
    @17
    @16
    lelttr
    syl3anc
    adantr
    mp2and
    df-2
    syl6breqr
    ex
    con3d
    @0
    @5
    @6
    @0
    @1
    c1
    cle
    wbr
    #
    @5
    @6
    wo
    #
    @0
    @9
    @26
    stle.1
    cA
    cS
    stle1
    mpi
    @0
    @10
    @21
    @26
    @27
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
end
