include "cn0.mm"
include "wcel.mm"
include "codd.mm"
include "c1.mm"
include "wceq.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cn.mm"
include "cc0.mm"
include "wi.mm"
include "elnn0.mm"
include "cuz.mm"
include "cfv.mm"
include "elnn1uz2.mm"
include "orc.mm"
include "a1d.mm"
include "cz.mm"
include "cle.mm"
include "wa.mm"
include "2z.mm"
include "eluz1i.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "zre.mm"
include "leloed.mm"
include "olc.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "wnel.mm"
include "2noddALTV.mm"
include "wn.mm"
include "df-nel.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "jaoi.mm"
include "imp.mm"
include "0noddALTV.mm"

theorem nn0o1gt2ALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ N e. Odd ) -> ( N = 1 \/ 2 < N ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    codd
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
    @1
    @4
    wi
    #
    cN
    elnn0
    @5
    @7
    @6
    @5
    @2
    cN
    c2
    cuz
    cfv
    wcel
    #
    wo
    @7
    cN
    elnn1uz2
    @2
    @7
    @8
    @2
    @4
    @1
    @2
    @3
    orc
    a1d
    @8
    cN
    cz
    wcel
    #
    c2
    cN
    cle
    wbr
    #
    wa
    @7
    c2
    cN
    2z
    eluz1i
    @9
    @10
    @7
    @9
    @10
    @3
    c2
    cN
    wceq
    #
    wo
    @7
    @9
    c2
    cN
    c2
    cr
    wcel
    @9
    2re
    a1i
    cN
    zre
    leloed
    @3
    @7
    @11
    @3
    @4
    @1
    @3
    @2
    olc
    a1d
    @11
    @1
    c2
    codd
    wcel
    #
    @4
    @1
    @12
    wb
    cN
    c2
    cN
    c2
    codd
    eleq1
    eqcoms
    c2
    codd
    wnel
    #
    @12
    @4
    wi
    #
    2noddALTV
    @13
    @12
    wn
    @14
    c2
    codd
    df-nel
    @12
    @4
    pm2.21
    sylbi
    ax-mp
    syl6bi
    jaoi
    syl6bi
    imp
    sylbi
    jaoi
    sylbi
    @6
    @1
    cc0
    codd
    wcel
    #
    @4
    cN
    cc0
    codd
    eleq1
    cc0
    codd
    wnel
    #
    @15
    @4
    wi
    #
    0noddALTV
    @16
    @15
    wn
    @17
    cc0
    codd
    df-nel
    @15
    @4
    pm2.21
    sylbi
    ax-mp
    syl6bi
    jaoi
    sylbi
    imp
end
