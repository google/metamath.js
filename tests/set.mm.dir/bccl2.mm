include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cbc.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "cz.mm"
include "elfz3nn0.mm"
include "elfzelz.mm"
include "bccl.mm"
include "syl2anc.mm"
include "bcrpcl.mm"
include "rpgt0d.mm"
include "elnnnn0b.mm"
include "sylanbrc.mm"

theorem bccl2
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n


  assert |- ( K e. ( 0 ... N ) -> ( N _C K ) e. NN )

  proof
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cK
    cbc
    co
    #
    cn0
    wcel
    #
    cc0
    @1
    clt
    wbr
    @1
    cn
    wcel
    @0
    cN
    cn0
    wcel
    cK
    cz
    wcel
    @2
    cK
    cN
    elfz3nn0
    cK
    cc0
    cN
    elfzelz
    cK
    cN
    bccl
    syl2anc
    @0
    @1
    cK
    cN
    bcrpcl
    rpgt0d
    @1
    elnnnn0b
    sylanbrc
end
