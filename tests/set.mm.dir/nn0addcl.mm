include "cn.mm"
include "cc.mm"
include "wss.mm"
include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "nnsscn.mm"
include "id.mm"
include "df-n0.mm"
include "nnaddcl.mm"
include "adantl.mm"
include "un0addcl.mm"
include "mpan.mm"

theorem nn0addcl
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( M + N ) e. NN0 )

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
    caddc
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
    nnaddcl
    adantl
    un0addcl
    mpan
end
