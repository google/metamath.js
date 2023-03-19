include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "codd.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "oddm1div2z.mm"
include "adantl.mm"
include "eluz2b1.mm"
include "1red.mm"
include "zre.mm"
include "posdifd.mm"
include "biimpa.mm"
include "cr.mm"
include "w3a.mm"
include "wb.mm"
include "peano2zm.mm"
include "zred.mm"
include "2re.mm"
include "a1i.mm"
include "2pos.mm"
include "3jca.mm"
include "adantr.mm"
include "gt0div.mm"
include "syl.mm"
include "mpbid.mm"
include "sylbi.mm"
include "elnnz.mm"
include "sylanbrc.mm"

theorem nnoALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. ( ZZ>= ` 2 ) /\ N e. Odd ) -> ( ( N - 1 ) / 2 ) e. NN )

  proof
    cN
    c2
    cuz
    cfv
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
    clt
    wbr
    #
    @3
    cn
    wcel
    @1
    @4
    @0
    cN
    oddm1div2z
    adantl
    @0
    @5
    @1
    @0
    cN
    cz
    wcel
    #
    c1
    cN
    clt
    wbr
    #
    wa
    #
    @5
    cN
    eluz2b1
    @8
    cc0
    @2
    clt
    wbr
    #
    @5
    @6
    @7
    @9
    @6
    c1
    cN
    @6
    1red
    cN
    zre
    posdifd
    biimpa
    @8
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
    w3a
    #
    @9
    @5
    wb
    @6
    @13
    @7
    @6
    @10
    @11
    @12
    @6
    @2
    cN
    peano2zm
    zred
    @11
    @6
    2re
    a1i
    @12
    @6
    2pos
    a1i
    3jca
    adantr
    @2
    c2
    gt0div
    syl
    mpbid
    sylbi
    adantr
    @3
    elnnz
    sylanbrc
end
