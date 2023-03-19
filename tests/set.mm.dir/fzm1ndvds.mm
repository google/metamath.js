include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cle.mm"
include "clt.mm"
include "wn.mm"
include "elfzle2.mm"
include "adantl.mm"
include "cz.mm"
include "wb.mm"
include "elfzelz.mm"
include "nnz.mm"
include "adantr.mm"
include "zltlem1.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "elfznn.mm"
include "nnred.mm"
include "cr.mm"
include "nnre.mm"
include "ltnled.mm"
include "mpbid.mm"
include "wi.mm"
include "dvdsle.mm"
include "mtod.mm"

theorem fzm1ndvds
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ N e. ( 1 ... ( M - 1 ) ) ) -> -. M || N )

  proof
    cM
    cn
    wcel
    #
    cN
    c1
    cM
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    cM
    cN
    cdvds
    wbr
    #
    cM
    cN
    cle
    wbr
    #
    @3
    cN
    cM
    clt
    wbr
    #
    @5
    wn
    @3
    @6
    cN
    @1
    cle
    wbr
    #
    @2
    @7
    @0
    cN
    c1
    @1
    elfzle2
    adantl
    @3
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @6
    @7
    wb
    @2
    @8
    @0
    cN
    c1
    @1
    elfzelz
    adantl
    @0
    @9
    @2
    cM
    nnz
    adantr
    #
    cN
    cM
    zltlem1
    syl2anc
    mpbird
    @3
    cN
    cM
    @3
    cN
    @2
    cN
    cn
    wcel
    #
    @0
    cN
    @1
    elfznn
    adantl
    #
    nnred
    @0
    cM
    cr
    wcel
    @2
    cM
    nnre
    adantr
    ltnled
    mpbid
    @3
    @9
    @11
    @4
    @5
    wi
    @10
    @12
    cM
    cN
    dvdsle
    syl2anc
    mtod
end
