include "cn.mm"
include "cc.mm"
include "wss.mm"
include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "nnsscn.mm"
include "id.mm"
include "df-n0.mm"
include "nnmulcl.mm"
include "adantl.mm"
include "un0mulcl.mm"
include "mpan.mm"

theorem nn0mulcl
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( M x. N ) e. NN0 )

  proof
    cn
    cc
    wss
    #
    cM
    cn0
    wcel
    cN
    cn0
    wcel
    wa
    cM
    cN
    cmul
    co
    #
    cn0
    wcel
    nnsscn
    @0
    cn
    cn0
    cM
    cN
    @0
    id
    df-n0
    cM
    cn
    wcel
    cN
    cn
    wcel
    wa
    @1
    cn
    wcel
    @0
    cM
    cN
    nnmulcl
    adantl
    un0mulcl
    mpan
end
