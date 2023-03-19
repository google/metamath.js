include "cn0.mm"
include "wcel.mm"
include "cprmo.mm"
include "cfv.mm"
include "cz.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "clcmf.mm"
include "cn.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cle.mm"
include "prmocl.mm"
include "nnzd.mm"
include "wss.mm"
include "cfn.mm"
include "cc0.mm"
include "wnel.mm"
include "fzssz.mm"
include "a1i.mm"
include "fzfid.mm"
include "0nelfz1.mm"
include "lcmfn0cl.mm"
include "syl3anc.mm"
include "jca.mm"
include "prmodvdslcmf.mm"
include "dvdsle.mm"
include "sylc.mm"

theorem prmolelcmf
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x


  assert |- ( N e. NN0 -> ( #p ` N ) <_ ( _lcm ` ( 1 ... N ) ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cprmo
    cfv
    #
    cz
    wcel
    #
    c1
    cN
    cfz
    co
    #
    clcmf
    cfv
    #
    cn
    wcel
    #
    wa
    @1
    @4
    cdvds
    wbr
    @1
    @4
    cle
    wbr
    @0
    @2
    @5
    @0
    @1
    cN
    prmocl
    nnzd
    @0
    @3
    cz
    wss
    #
    @3
    cfn
    wcel
    cc0
    @3
    wnel
    #
    @5
    @6
    @0
    c1
    cN
    fzssz
    a1i
    @0
    c1
    cN
    fzfid
    @7
    @0
    cN
    0nelfz1
    a1i
    @3
    lcmfn0cl
    syl3anc
    jca
    cN
    prmodvdslcmf
    @1
    @4
    dvdsle
    sylc
end
