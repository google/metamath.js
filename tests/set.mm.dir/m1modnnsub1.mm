include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cmo.mm"
include "co.mm"
include "cmin.mm"
include "cr.mm"
include "crp.mm"
include "wceq.mm"
include "1re.mm"
include "nnrp.mm"
include "negmod.mm"
include "sylancr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "nnre.mm"
include "peano2rem.mm"
include "syl.mm"
include "nnm1ge0.mm"
include "ltm1d.mm"
include "modid.mm"
include "syl22anc.mm"
include "eqtrd.mm"

theorem m1modnnsub1
  let cM: class M


  assert |- ( M e. NN -> ( -u 1 mod M ) = ( M - 1 ) )

  proof
    cM
    cn
    wcel
    #
    c1
    cneg
    cM
    cmo
    co
    #
    cM
    c1
    cmin
    co
    #
    cM
    cmo
    co
    #
    @2
    @0
    c1
    cr
    wcel
    cM
    crp
    wcel
    #
    @1
    @3
    wceq
    1re
    cM
    nnrp
    #
    c1
    cM
    negmod
    sylancr
    @0
    @2
    cr
    wcel
    #
    @4
    cc0
    @2
    cle
    wbr
    @2
    cM
    clt
    wbr
    @3
    @2
    wceq
    @0
    cM
    cr
    wcel
    @6
    cM
    nnre
    #
    cM
    peano2rem
    syl
    @5
    cM
    nnm1ge0
    @0
    cM
    @7
    ltm1d
    @2
    cM
    modid
    syl22anc
    eqtrd
end
