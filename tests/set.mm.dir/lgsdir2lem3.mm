include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "c8.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "c7.mm"
include "cfz.mm"
include "c1.mm"
include "cpr.mm"
include "c3.mm"
include "c5.mm"
include "cun.mm"
include "cmin.mm"
include "cn.mm"
include "simpl.mm"
include "8nn.mm"
include "zmodfz.mm"
include "sylancl.mm"
include "8cn.mm"
include "ax-1cn.mm"
include "7cn.mm"
include "caddc.mm"
include "addcomi.mm"
include "df-8.mm"
include "eqtr4i.mm"
include "subaddrii.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "wi.mm"
include "c6.mm"
include "c4.mm"
include "cneg.mm"
include "neg1z.mm"
include "2z.mm"
include "dvds0.mm"
include "ax-mp.mm"
include "1pneg1e0.mm"
include "neg1cn.mm"
include "eqtr3i.mm"
include "breqtri.mm"
include "c0.mm"
include "noel.mm"
include "pm2.21i.mm"
include "clt.mm"
include "wceq.mm"
include "neg1lt0.mm"
include "wb.mm"
include "0z.mm"
include "fzn.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eleq2s.mm"
include "a1i.mm"
include "3pm3.2i.mm"
include "1e0p1.mm"
include "ssun1.mm"
include "1ex.mm"
include "prid1.mm"
include "sselii.mm"
include "lgsdir2lem2.mm"
include "df-2.mm"
include "df-3.mm"
include "ssun2.mm"
include "3ex.mm"
include "df-4.mm"
include "df-5.mm"
include "5nn.mm"
include "elexi.mm"
include "prid2.mm"
include "df-6.mm"
include "df-7.mm"
include "7nn.mm"
include "simp3i.mm"
include "mpd.mm"

theorem lgsdir2lem3
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let cM: class M
  let cP: class P
  let wph: wff ph
  let vp: setvar p
  let cN: class N


  assert |- ( ( A e. ZZ /\ -. 2 || A ) -> ( A mod 8 ) e. ( { 1 , 7 } u. { 3 , 5 } ) )

  proof
    cA
    cz
    wcel
    #
    c2
    cA
    cdvds
    wbr
    wn
    #
    wa
    #
    cA
    c8
    cmo
    co
    #
    cc0
    c7
    cfz
    co
    #
    wcel
    #
    @3
    c1
    c7
    cpr
    #
    c3
    c5
    cpr
    #
    cun
    #
    wcel
    #
    @2
    @3
    cc0
    c8
    c1
    cmin
    co
    #
    cfz
    co
    #
    @4
    @2
    @0
    c8
    cn
    wcel
    @3
    @11
    wcel
    @0
    @1
    simpl
    8nn
    cA
    c8
    zmodfz
    sylancl
    @10
    c7
    cc0
    cfz
    c8
    c1
    c7
    8cn
    ax-1cn
    7cn
    c1
    c7
    caddc
    co
    c7
    c1
    caddc
    co
    #
    c8
    c1
    c7
    ax-1cn
    7cn
    addcomi
    df-8
    eqtr4i
    subaddrii
    oveq2i
    syl6eleq
    c7
    cz
    wcel
    c2
    @12
    cdvds
    wbr
    @2
    @5
    @9
    wi
    wi
    cA
    @8
    c5
    c6
    c7
    cA
    @8
    c3
    c4
    c5
    cA
    @8
    c1
    c2
    c3
    cA
    @8
    c1
    cneg
    #
    cc0
    c1
    @13
    cz
    wcel
    #
    c2
    @13
    c1
    caddc
    co
    #
    cdvds
    wbr
    @2
    @3
    cc0
    @13
    cfz
    co
    #
    wcel
    @9
    wi
    #
    wi
    neg1z
    c2
    cc0
    @15
    cdvds
    c2
    cz
    wcel
    c2
    cc0
    cdvds
    wbr
    2z
    c2
    dvds0
    ax-mp
    c1
    @13
    caddc
    co
    cc0
    @15
    1pneg1e0
    c1
    @13
    ax-1cn
    neg1cn
    addcomi
    eqtr3i
    #
    breqtri
    @17
    @2
    @9
    @3
    c0
    @16
    @3
    c0
    wcel
    @9
    @3
    noel
    pm2.21i
    @13
    cc0
    clt
    wbr
    #
    @16
    c0
    wceq
    #
    neg1lt0
    cc0
    cz
    wcel
    @14
    @19
    @20
    wb
    0z
    neg1z
    cc0
    @13
    fzn
    mp2an
    mpbi
    eleq2s
    a1i
    3pm3.2i
    @18
    1e0p1
    @6
    @8
    c1
    @6
    @7
    ssun1
    #
    c1
    c7
    1ex
    prid1
    sselii
    lgsdir2lem2
    df-2
    df-3
    @7
    @8
    c3
    @7
    @6
    ssun2
    #
    c3
    c5
    3ex
    prid1
    sselii
    lgsdir2lem2
    df-4
    df-5
    @7
    @8
    c5
    @22
    c3
    c5
    c5
    cn
    5nn
    elexi
    prid2
    sselii
    lgsdir2lem2
    df-6
    df-7
    @6
    @8
    c7
    @21
    c1
    c7
    c7
    cn
    7nn
    elexi
    prid2
    sselii
    lgsdir2lem2
    simp3i
    mpd
end
