include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "cmin.mm"
include "cn.mm"
include "wi.mm"
include "nnge1.mm"
include "a1i.mm"
include "znnsub.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "1re.mm"
include "leaddsub2.mm"
include "mp3an2.mm"
include "syl2an.mm"
include "3imtr4d.mm"
include "adantr.mm"
include "ltp1d.mm"
include "peano2re.mm"
include "syl.mm"
include "adantl.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "impbid.mm"

theorem zltp1le
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M < N <-> ( M + 1 ) <_ N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cN
    clt
    wbr
    #
    cM
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @2
    cN
    cM
    cmin
    co
    #
    cn
    wcel
    #
    c1
    @6
    cle
    wbr
    #
    @3
    @5
    @7
    @8
    wi
    @2
    @6
    nnge1
    a1i
    cM
    cN
    znnsub
    @0
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @5
    @8
    wb
    #
    @1
    cM
    zre
    #
    cN
    zre
    #
    @9
    c1
    cr
    wcel
    @10
    @11
    1re
    cM
    c1
    cN
    leaddsub2
    mp3an2
    syl2an
    3imtr4d
    @2
    cM
    @4
    clt
    wbr
    #
    @5
    @3
    @2
    cM
    @0
    @9
    @1
    @12
    adantr
    #
    ltp1d
    @2
    @9
    @4
    cr
    wcel
    #
    @10
    @14
    @5
    wa
    @3
    wi
    @15
    @2
    @9
    @16
    @15
    cM
    peano2re
    syl
    @1
    @10
    @0
    @13
    adantl
    cM
    @4
    cN
    ltletr
    syl3anc
    mpand
    impbid
end
