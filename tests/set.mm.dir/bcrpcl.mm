include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cbc.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "crp.mm"
include "bcval2.mm"
include "cn.mm"
include "cn0.mm"
include "elfz3nn0.mm"
include "faccl.mm"
include "syl.mm"
include "fznn0sub.mm"
include "elfznn0.mm"
include "nnmulcl.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "nnrp.mm"
include "rpdivcl.mm"
include "eqeltrd.mm"

theorem bcrpcl
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 0 ... N ) -> ( N _C K ) e. RR+ )

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
    cN
    cfa
    cfv
    #
    cN
    cK
    cmin
    co
    #
    cfa
    cfv
    #
    cK
    cfa
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    crp
    cK
    cN
    bcval2
    @0
    @1
    cn
    wcel
    #
    @5
    cn
    wcel
    #
    @6
    crp
    wcel
    #
    @0
    cN
    cn0
    wcel
    @7
    cK
    cN
    elfz3nn0
    cN
    faccl
    syl
    @0
    @2
    cn0
    wcel
    #
    cK
    cn0
    wcel
    #
    @8
    cK
    cc0
    cN
    fznn0sub
    cK
    cN
    elfznn0
    @10
    @3
    cn
    wcel
    @4
    cn
    wcel
    @8
    @11
    @2
    faccl
    cK
    faccl
    @3
    @4
    nnmulcl
    syl2an
    syl2anc
    @7
    @1
    crp
    wcel
    @5
    crp
    wcel
    @9
    @8
    @1
    nnrp
    @5
    nnrp
    @1
    @5
    rpdivcl
    syl2an
    syl2anc
    eqeltrd
end
