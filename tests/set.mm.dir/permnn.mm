include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfa.mm"
include "cfv.mm"
include "cn.mm"
include "cmin.mm"
include "cmul.mm"
include "cc.mm"
include "cdiv.mm"
include "cn0.mm"
include "elfznn0.mm"
include "faccl.mm"
include "syl.mm"
include "fznn0sub.mm"
include "nnmulcld.mm"
include "elfz3nn0.mm"
include "nncnd.mm"
include "wne.mm"
include "facne0.mm"
include "divcan4d.mm"
include "eqeltrd.mm"
include "cbc.mm"
include "bcval2.mm"
include "bccl2.mm"
include "eqeltrrd.mm"
include "nndivtr.mm"
include "syl32anc.mm"

theorem permnn
  let cR: class R
  let cN: class N


  assert |- ( R e. ( 0 ... N ) -> ( ( ! ` N ) / ( ! ` R ) ) e. NN )

  proof
    cR
    cc0
    cN
    cfz
    co
    wcel
    #
    cR
    cfa
    cfv
    #
    cn
    wcel
    #
    cN
    cR
    cmin
    co
    #
    cfa
    cfv
    #
    @1
    cmul
    co
    #
    cn
    wcel
    cN
    cfa
    cfv
    #
    cc
    wcel
    #
    @5
    @1
    cdiv
    co
    #
    cn
    wcel
    @6
    @5
    cdiv
    co
    #
    cn
    wcel
    @6
    @1
    cdiv
    co
    cn
    wcel
    @0
    cR
    cn0
    wcel
    #
    @2
    cR
    cN
    elfznn0
    #
    cR
    faccl
    syl
    #
    @0
    @4
    @1
    @0
    @3
    cn0
    wcel
    @4
    cn
    wcel
    cR
    cc0
    cN
    fznn0sub
    @3
    faccl
    syl
    #
    @12
    nnmulcld
    @0
    cN
    cn0
    wcel
    #
    @7
    cR
    cN
    elfz3nn0
    @14
    @6
    cN
    faccl
    nncnd
    syl
    @0
    @8
    @4
    cn
    @0
    @4
    @1
    @0
    @4
    @13
    nncnd
    @0
    @1
    @12
    nncnd
    @0
    @10
    @1
    cc0
    wne
    @11
    cR
    facne0
    syl
    divcan4d
    @13
    eqeltrd
    @0
    cN
    cR
    cbc
    co
    @9
    cn
    cR
    cN
    bcval2
    cR
    cN
    bccl2
    eqeltrrd
    @1
    @5
    @6
    nndivtr
    syl32anc
end
