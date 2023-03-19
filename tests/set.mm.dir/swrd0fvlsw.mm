include "cword.mm"
include "wcel.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cmin.mm"
include "wceq.mm"
include "swrdcl.mm"
include "adantr.mm"
include "lsw.mm"
include "syl.mm"
include "cuz.mm"
include "wss.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "ax-mp.mm"
include "sseli.mm"
include "swrd0len.mm"
include "sylan2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "cfzo.mm"
include "simpl.mm"
include "adantl.mm"
include "cn.mm"
include "elfznn.mm"
include "fzo0end.mm"
include "swrd0fv.mm"
include "syl3anc.mm"
include "3eqtrd.mm"

theorem swrd0fvlsw
  let cL: class L
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ L e. ( 1 ... ( # ` W ) ) ) -> ( lastS ` ( W substr <. 0 , L >. ) ) = ( W ` ( L - 1 ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cL
    c1
    cW
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cW
    cc0
    cL
    cop
    csubstr
    co
    #
    clsw
    cfv
    #
    @6
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @6
    cfv
    #
    cL
    c1
    cmin
    co
    #
    @6
    cfv
    #
    @11
    cW
    cfv
    #
    @5
    @6
    @0
    wcel
    #
    @7
    @10
    wceq
    @1
    @14
    @4
    cV
    cW
    cc0
    cL
    swrdcl
    adantr
    @6
    @0
    lsw
    syl
    @5
    @9
    @11
    @6
    @5
    @8
    cL
    c1
    cmin
    @4
    @1
    cL
    cc0
    @2
    cfz
    co
    #
    wcel
    #
    @8
    cL
    wceq
    @3
    @15
    cL
    c1
    cc0
    cuz
    cfv
    wcel
    @3
    @15
    wss
    1eluzge0
    c1
    cc0
    @2
    fzss1
    ax-mp
    sseli
    #
    cV
    cW
    cL
    swrd0len
    sylan2
    oveq1d
    fveq2d
    @5
    @1
    @16
    @11
    cc0
    cL
    cfzo
    co
    wcel
    #
    @12
    @13
    wceq
    @1
    @4
    simpl
    @4
    @16
    @1
    @17
    adantl
    @4
    @18
    @1
    @4
    cL
    cn
    wcel
    @18
    cL
    @2
    elfznn
    cL
    fzo0end
    syl
    adantl
    @11
    cL
    cV
    cW
    swrd0fv
    syl3anc
    3eqtrd
end
