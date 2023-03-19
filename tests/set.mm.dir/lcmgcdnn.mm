include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "clcm.mm"
include "co.mm"
include "cgcd.mm"
include "cmul.mm"
include "cabs.mm"
include "cfv.mm"
include "cz.mm"
include "wceq.mm"
include "nnz.mm"
include "lcmgcd.mm"
include "syl2an.mm"
include "cn0.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nnmulcl.mm"
include "nnnn0d.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "jca.mm"
include "absid.mm"
include "3syl.mm"
include "eqtrd.mm"

theorem lcmgcdnn
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ N e. NN ) -> ( ( M lcm N ) x. ( M gcd N ) ) = ( M x. N ) )

  proof
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cM
    cN
    clcm
    co
    cM
    cN
    cgcd
    co
    cmul
    co
    #
    cM
    cN
    cmul
    co
    #
    cabs
    cfv
    #
    @4
    @0
    cM
    cz
    wcel
    cN
    cz
    wcel
    @3
    @5
    wceq
    @1
    cM
    nnz
    cN
    nnz
    cM
    cN
    lcmgcd
    syl2an
    @2
    @4
    cn0
    wcel
    #
    @4
    cr
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    wa
    @5
    @4
    wceq
    @2
    @4
    cM
    cN
    nnmulcl
    nnnn0d
    @6
    @7
    @8
    @4
    nn0re
    @4
    nn0ge0
    jca
    @4
    absid
    3syl
    eqtrd
end
