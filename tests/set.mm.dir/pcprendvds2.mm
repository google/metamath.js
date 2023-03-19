include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "pcprendvds.mm"
include "cmul.mm"
include "wi.mm"
include "cn.mm"
include "eluz2nn.mm"
include "adantr.mm"
include "nnzd.mm"
include "cn0.mm"
include "pcprecl.mm"
include "simprd.mm"
include "wb.mm"
include "simpld.mm"
include "nnexpcld.mm"
include "nnne0d.mm"
include "simprl.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "dvdscmul.mm"
include "nncnd.mm"
include "expp1d.mm"
include "eqcomd.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "divcan2d.mm"
include "breq12d.mm"
include "sylibd.mm"
include "mtod.mm"

theorem pcprendvds2
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
  assert |- ( ( P e. ( ZZ>= ` 2 ) /\ ( N e. ZZ /\ N =/= 0 ) ) -> -. P || ( N / ( P ^ S ) ) )

  proof
    cP
    c2
    cuz
    cfv
    wcel
    #
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
    wa
    #
    cP
    cN
    cP
    cS
    cexp
    co
    #
    cdiv
    co
    #
    cdvds
    wbr
    #
    cP
    cS
    c1
    caddc
    co
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    cA
    cP
    cS
    vn
    cN
    pclem.1
    pclem.2
    pcprendvds
    @4
    @7
    @5
    cP
    cmul
    co
    #
    @5
    @6
    cmul
    co
    #
    cdvds
    wbr
    #
    @9
    @4
    cP
    cz
    wcel
    @6
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @7
    @12
    wi
    @4
    cP
    @0
    cP
    cn
    wcel
    @3
    cP
    eluz2nn
    adantr
    #
    nnzd
    @4
    @5
    cN
    cdvds
    wbr
    #
    @13
    @4
    cS
    cn0
    wcel
    #
    @16
    cA
    cP
    cS
    vn
    cN
    pclem.1
    pclem.2
    pcprecl
    #
    simprd
    @4
    @14
    @5
    cc0
    wne
    @1
    @16
    @13
    wb
    @4
    @5
    @4
    cP
    cS
    @15
    @4
    @17
    @16
    @18
    simpld
    #
    nnexpcld
    #
    nnzd
    #
    @4
    @5
    @20
    nnne0d
    #
    @0
    @1
    @2
    simprl
    @5
    cN
    dvdsval2
    syl3anc
    mpbid
    @21
    @5
    cP
    @6
    dvdscmul
    syl3anc
    @4
    @10
    @8
    @11
    cN
    cdvds
    @4
    @8
    @10
    @4
    cP
    cS
    @4
    cP
    @15
    nncnd
    @19
    expp1d
    eqcomd
    @4
    cN
    @5
    @1
    cN
    cc
    wcel
    @0
    @2
    cN
    zcn
    ad2antrl
    @4
    @5
    @20
    nncnd
    @22
    divcan2d
    breq12d
    sylibd
    mtod
end
