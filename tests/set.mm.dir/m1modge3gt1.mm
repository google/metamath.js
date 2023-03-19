include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "cmo.mm"
include "clt.mm"
include "caddc.mm"
include "wbr.mm"
include "c2.mm"
include "1p1e2.mm"
include "cle.mm"
include "2p1e3.mm"
include "eluzle.mm"
include "syl5eqbr.mm"
include "cz.mm"
include "wb.mm"
include "2z.mm"
include "eluzelz.mm"
include "zltp1le.mm"
include "sylancr.mm"
include "mpbird.mm"
include "1red.mm"
include "eluzelre.mm"
include "ltaddsub2d.mm"
include "mpbid.mm"
include "cn.mm"
include "wceq.mm"
include "eluzge3nn.mm"
include "m1modnnsub1.mm"
include "syl.mm"
include "breqtrrd.mm"

theorem m1modge3gt1
  let cM: class M


  assert |- ( M e. ( ZZ>= ` 3 ) -> 1 < ( -u 1 mod M ) )

  proof
    cM
    c3
    cuz
    cfv
    wcel
    #
    c1
    cM
    c1
    cmin
    co
    #
    c1
    cneg
    cM
    cmo
    co
    #
    clt
    @0
    c1
    c1
    caddc
    co
    #
    cM
    clt
    wbr
    c1
    @1
    clt
    wbr
    @0
    @3
    c2
    cM
    clt
    1p1e2
    @0
    c2
    cM
    clt
    wbr
    #
    c2
    c1
    caddc
    co
    #
    cM
    cle
    wbr
    #
    @0
    @5
    c3
    cM
    cle
    2p1e3
    c3
    cM
    eluzle
    syl5eqbr
    @0
    c2
    cz
    wcel
    cM
    cz
    wcel
    @4
    @6
    wb
    2z
    c3
    cM
    eluzelz
    c2
    cM
    zltp1le
    sylancr
    mpbird
    syl5eqbr
    @0
    c1
    c1
    cM
    @0
    1red
    #
    @7
    c3
    cM
    eluzelre
    ltaddsub2d
    mpbid
    @0
    cM
    cn
    wcel
    @2
    @1
    wceq
    cM
    eluzge3nn
    cM
    m1modnnsub1
    syl
    breqtrrd
end
