include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cop.mm"
include "csubstr.mm"
include "caddc.mm"
include "cmin.mm"
include "swrdrlen.mm"
include "swrd0len.mm"
include "oveq12d.mm"
include "cn0.mm"
include "cz.mm"
include "wceq.mm"
include "lencl.mm"
include "elfzelz.mm"
include "cc.mm"
include "nn0cn.mm"
include "zcn.mm"
include "npcan.mm"
include "syl2an.mm"
include "eqtrd.mm"

theorem addlenrevswrd
  let cM: class M
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ M e. ( 0 ... ( # ` W ) ) ) -> ( ( # ` ( W substr <. M , ( # ` W ) >. ) ) + ( # ` ( W substr <. 0 , M >. ) ) ) = ( # ` W ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cM
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    cW
    cM
    @1
    cop
    csubstr
    co
    chash
    cfv
    #
    cW
    cc0
    cM
    cop
    csubstr
    co
    chash
    cfv
    #
    caddc
    co
    @1
    cM
    cmin
    co
    #
    cM
    caddc
    co
    #
    @1
    @3
    @4
    @6
    @5
    cM
    caddc
    cM
    cV
    cW
    swrdrlen
    cV
    cW
    cM
    swrd0len
    oveq12d
    @0
    @1
    cn0
    wcel
    #
    cM
    cz
    wcel
    #
    @7
    @1
    wceq
    #
    @2
    cV
    cW
    lencl
    cM
    cc0
    @1
    elfzelz
    @8
    @1
    cc
    wcel
    cM
    cc
    wcel
    @10
    @9
    @1
    nn0cn
    cM
    zcn
    @1
    cM
    npcan
    syl2an
    syl2an
    eqtrd
end
