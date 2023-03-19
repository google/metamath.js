include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "cn0.mm"
include "cz.mm"
include "wne.mm"
include "1z.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "ax-1ne0.mm"
include "neeq1.mm"
include "jca.mm"
include "pcprecl.mm"
include "sylan2.mm"
include "simprd.mm"
include "simpr.mm"
include "breqtrd.mm"
include "cn.mm"
include "wi.mm"
include "eluz2nn.mm"
include "adantr.mm"
include "simpld.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "1nn.mm"
include "dvdsle.mm"
include "sylancl.mm"
include "mpd.mm"
include "nncnd.mm"
include "exp0d.mm"
include "breqtrrd.mm"
include "nnred.mm"
include "nn0zd.mm"
include "0zd.mm"
include "clt.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "leexp2d.mm"
include "mpbird.mm"
include "wb.mm"
include "nn0le0eq0.mm"
include "syl.mm"
include "mpbid.mm"

theorem pcpre1
  let cA: class A
  let cP: class P
  let cS: class S
  let vn: setvar n
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pclem.1: |- A = { n e. NN0 | ( P ^ n ) || N }
  assume pclem.2: |- S = sup ( A , RR , < )

  disjoint N n
  disjoint P n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint S x
  assert |- ( ( P e. ( ZZ>= ` 2 ) /\ N = 1 ) -> S = 0 )

  proof
    cP
    c2
    cuz
    cfv
    wcel
    #
    cN
    c1
    wceq
    #
    wa
    #
    cS
    cc0
    cle
    wbr
    #
    cS
    cc0
    wceq
    #
    @2
    @3
    cP
    cS
    cexp
    co
    #
    cP
    cc0
    cexp
    co
    #
    cle
    wbr
    @2
    @5
    c1
    @6
    cle
    @2
    @5
    c1
    cdvds
    wbr
    #
    @5
    c1
    cle
    wbr
    #
    @2
    @5
    cN
    c1
    cdvds
    @2
    cS
    cn0
    wcel
    #
    @5
    cN
    cdvds
    wbr
    #
    @1
    @0
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    #
    @9
    @10
    wa
    @1
    @11
    @12
    @1
    @11
    c1
    cz
    wcel
    1z
    cN
    c1
    cz
    eleq1
    mpbiri
    @1
    @12
    c1
    cc0
    wne
    ax-1ne0
    cN
    c1
    cc0
    neeq1
    mpbiri
    jca
    #
    cA
    cP
    cS
    vn
    cN
    pclem.1
    pclem.2
    pcprecl
    #
    sylan2
    #
    simprd
    @0
    @1
    simpr
    breqtrd
    @2
    @5
    cz
    wcel
    c1
    cn
    wcel
    @7
    @8
    wi
    @2
    @5
    @2
    cP
    cS
    @0
    cP
    cn
    wcel
    #
    @1
    cP
    eluz2nn
    adantr
    #
    @2
    @9
    @10
    @16
    simpld
    #
    nnexpcld
    nnzd
    1nn
    @5
    c1
    dvdsle
    sylancl
    mpd
    @2
    cP
    @2
    cP
    @18
    nncnd
    exp0d
    breqtrrd
    @2
    cP
    cS
    cc0
    @2
    cP
    @18
    nnred
    @2
    cS
    @19
    nn0zd
    @2
    0zd
    @0
    c1
    cP
    clt
    wbr
    #
    @1
    @0
    @17
    @20
    cP
    eluz2b2
    simprbi
    adantr
    leexp2d
    mpbird
    @2
    @9
    @3
    @4
    wb
    @1
    @0
    @13
    @9
    @14
    @0
    @13
    wa
    @9
    @10
    @15
    simpld
    sylan2
    cS
    nn0le0eq0
    syl
    mpbid
end
