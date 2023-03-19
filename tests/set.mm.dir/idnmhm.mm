include "cnlm.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "clmhm.mm"
include "co.mm"
include "cnghm.mm"
include "cnmhm.mm"
include "id.mm"
include "jca.mm"
include "clmod.mm"
include "nlmlmod.mm"
include "idlmhm.mm"
include "syl.mm"
include "cngp.mm"
include "nlmngp.mm"
include "idnghm.mm"
include "isnmhm.mm"
include "sylanbrc.mm"

theorem idnmhm
  let cS: class S
  let cV: class V
  assume 0nmhm.1: |- V = ( Base ` S )


  assert |- ( S e. NrmMod -> ( _I |` V ) e. ( S NMHom S ) )

  proof
    cS
    cnlm
    wcel
    #
    @0
    @0
    wa
    cid
    cV
    cres
    #
    cS
    cS
    clmhm
    co
    wcel
    #
    @1
    cS
    cS
    cnghm
    co
    wcel
    #
    wa
    @1
    cS
    cS
    cnmhm
    co
    wcel
    @0
    @0
    @0
    @0
    id
    #
    @4
    jca
    @0
    @2
    @3
    @0
    cS
    clmod
    wcel
    @2
    cS
    nlmlmod
    cV
    cS
    0nmhm.1
    idlmhm
    syl
    @0
    cS
    cngp
    wcel
    @3
    cS
    nlmngp
    cS
    cV
    0nmhm.1
    idnghm
    syl
    jca
    cS
    cS
    @1
    isnmhm
    sylanbrc
end
