include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "wo.mm"
include "cmin.mm"
include "cfl.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "nn0eo.mm"
include "wi.mm"
include "wa.mm"
include "cr.mm"
include "nn0re.mm"
include "peano2rem.mm"
include "syl.mm"
include "adantl.mm"
include "crp.mm"
include "2rp.mm"
include "a1i.mm"
include "lem1d.mm"
include "lediv1dd.mm"
include "wceq.mm"
include "cz.mm"
include "nn0z.mm"
include "flid.mm"
include "adantr.mm"
include "breqtrrd.mm"
include "ex.mm"
include "nn0o.mm"
include "rehalfcld.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lediv1.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "flwordi.mm"
include "eqbrtrrd.mm"
include "syldc.mm"
include "jaoi.mm"
include "mpcom.mm"

theorem flnn0div2ge
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN0 -> ( ( N - 1 ) / 2 ) <_ ( |_ ` ( N / 2 ) ) )

  proof
    cN
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    cn0
    wcel
    #
    wo
    cN
    cn0
    wcel
    #
    cN
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    @0
    cfl
    cfv
    #
    cle
    wbr
    #
    cN
    nn0eo
    @1
    @3
    @7
    wi
    @2
    @1
    @3
    @7
    @1
    @3
    wa
    #
    @5
    @0
    @6
    cle
    @8
    @4
    cN
    c2
    @3
    @4
    cr
    wcel
    #
    @1
    @3
    cN
    cr
    wcel
    #
    @9
    cN
    nn0re
    #
    cN
    peano2rem
    syl
    #
    adantl
    @3
    @10
    @1
    @11
    adantl
    c2
    crp
    wcel
    @8
    2rp
    a1i
    @3
    @4
    cN
    cle
    wbr
    #
    @1
    @3
    cN
    @11
    lem1d
    #
    adantl
    lediv1dd
    @1
    @6
    @0
    wceq
    #
    @3
    @1
    @0
    cz
    wcel
    @15
    @0
    nn0z
    @0
    flid
    syl
    adantr
    breqtrrd
    ex
    @3
    @2
    @5
    cn0
    wcel
    #
    @7
    @3
    @2
    @16
    cN
    nn0o
    ex
    @3
    @16
    @7
    @3
    @16
    wa
    #
    @5
    cfl
    cfv
    #
    @5
    @6
    cle
    @17
    @5
    cz
    wcel
    #
    @18
    @5
    wceq
    @16
    @19
    @3
    @5
    nn0z
    adantl
    @5
    flid
    syl
    @17
    @5
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    @5
    @0
    cle
    wbr
    #
    @18
    @6
    cle
    wbr
    @3
    @20
    @16
    @3
    @4
    @12
    rehalfcld
    adantr
    @3
    @21
    @16
    @3
    cN
    @11
    rehalfcld
    adantr
    @3
    @22
    @16
    @3
    @13
    @22
    @14
    @3
    @9
    @10
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @13
    @22
    wb
    @12
    @11
    @25
    @3
    @23
    @24
    2re
    2pos
    pm3.2i
    a1i
    @4
    cN
    c2
    lediv1
    syl3anc
    mpbid
    adantr
    @5
    @0
    flwordi
    syl3anc
    eqbrtrrd
    ex
    syldc
    jaoi
    mpcom
end
