include "cn0.mm"
include "wcel.mm"
include "codd.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cz.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "oddm1div2z.mm"
include "adantl.mm"
include "cn.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elnn0.mm"
include "nnm1ge0.mm"
include "cr.mm"
include "clt.mm"
include "wb.mm"
include "nnre.mm"
include "peano2rem.mm"
include "syl.mm"
include "2re.mm"
include "a1i.mm"
include "2pos.mm"
include "ge0div.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "a1d.mm"
include "eleq1.mm"
include "wnel.mm"
include "0noddALTV.mm"
include "wn.mm"
include "df-nel.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "jaoi.mm"
include "imp.mm"
include "elnn0z.mm"
include "sylanbrc.mm"

theorem nn0oALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ N e. Odd ) -> ( ( N - 1 ) / 2 ) e. NN0 )

  proof
    cN
    cn0
    wcel
    #
    cN
    codd
    wcel
    #
    wa
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @3
    cn0
    wcel
    @1
    @4
    @0
    cN
    oddm1div2z
    adantl
    @0
    @1
    @5
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
    @1
    @5
    wi
    #
    cN
    elnn0
    @6
    @8
    @7
    @6
    @5
    @1
    @6
    cc0
    @2
    cle
    wbr
    #
    @5
    cN
    nnm1ge0
    @6
    @2
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @9
    @5
    wb
    @6
    cN
    cr
    wcel
    @10
    cN
    nnre
    cN
    peano2rem
    syl
    @11
    @6
    2re
    a1i
    @12
    @6
    2pos
    a1i
    @2
    c2
    ge0div
    syl3anc
    mpbid
    a1d
    @7
    @1
    cc0
    codd
    wcel
    #
    @5
    cN
    cc0
    codd
    eleq1
    cc0
    codd
    wnel
    #
    @13
    @5
    wi
    #
    0noddALTV
    @14
    @13
    wn
    @15
    cc0
    codd
    df-nel
    @13
    @5
    pm2.21
    sylbi
    ax-mp
    syl6bi
    jaoi
    sylbi
    imp
    @3
    elnn0z
    sylanbrc
end
