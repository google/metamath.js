include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cn0.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "eluz2nn.mm"
include "dvdsprmpweq.mm"
include "syl3an2.mm"
include "imp.mm"
include "cc0.mm"
include "csn.mm"
include "wo.mm"
include "cun.mm"
include "df-n0.mm"
include "rexeqi.mm"
include "rexun.mm"
include "bitri.mm"
include "cz.mm"
include "wb.mm"
include "0z.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rexsng.mm"
include "ax-mp.mm"
include "c1.mm"
include "prmnn.mm"
include "nncnd.mm"
include "exp0d.mm"
include "3ad2ant1.mm"
include "wne.mm"
include "eluz2b3.mm"
include "eqneqall.mm"
include "com12.mm"
include "simplbiim.mm"
include "3ad2ant2.mm"
include "sylbid.mm"
include "impd.mm"
include "sylbi.mm"
include "jao1i.mm"
include "mpcom.mm"
include "ex.mm"

theorem dvdsprmpweqnn
  let cA: class A
  let cP: class P
  let vn: setvar n
  let cN: class N

  disjoint A n
  disjoint N n
  disjoint P n
  assert |- ( ( P e. Prime /\ A e. ( ZZ>= ` 2 ) /\ N e. NN0 ) -> ( A || ( P ^ N ) -> E. n e. NN A = ( P ^ n ) ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    c2
    cuz
    cfv
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cA
    cP
    cN
    cexp
    co
    cdvds
    wbr
    #
    cA
    cP
    vn
    cv
    #
    cexp
    co
    #
    wceq
    #
    vn
    cn
    wrex
    #
    @7
    vn
    cn0
    wrex
    #
    @3
    @4
    wa
    #
    @8
    @3
    @4
    @9
    @1
    @0
    cA
    cn
    wcel
    #
    @2
    @4
    @9
    wi
    cA
    eluz2nn
    cA
    cP
    vn
    cN
    dvdsprmpweq
    syl3an2
    imp
    @9
    @8
    @7
    vn
    cc0
    csn
    #
    wrex
    #
    wo
    #
    @10
    @8
    wi
    #
    @9
    @7
    vn
    cn
    @12
    cun
    #
    wrex
    @14
    @7
    vn
    cn0
    @16
    df-n0
    rexeqi
    @7
    vn
    cn
    @12
    rexun
    bitri
    @8
    @13
    @10
    @13
    cA
    cP
    cc0
    cexp
    co
    #
    wceq
    #
    @15
    cc0
    cz
    wcel
    @13
    @18
    wb
    0z
    @7
    @18
    vn
    cc0
    cz
    @5
    cc0
    wceq
    @6
    @17
    cA
    @5
    cc0
    cP
    cexp
    oveq2
    eqeq2d
    rexsng
    ax-mp
    @18
    @3
    @4
    @8
    @3
    @18
    @4
    @8
    wi
    #
    @3
    @18
    cA
    c1
    wceq
    #
    @19
    @3
    @17
    c1
    cA
    @0
    @1
    @17
    c1
    wceq
    @2
    @0
    cP
    @0
    cP
    cP
    prmnn
    nncnd
    exp0d
    3ad2ant1
    eqeq2d
    @1
    @0
    @20
    @19
    wi
    #
    @2
    @1
    @11
    cA
    c1
    wne
    #
    @21
    cA
    eluz2b3
    @20
    @22
    @19
    @19
    cA
    c1
    eqneqall
    com12
    simplbiim
    3ad2ant2
    sylbid
    com12
    impd
    sylbi
    jao1i
    sylbi
    mpcom
    ex
end
