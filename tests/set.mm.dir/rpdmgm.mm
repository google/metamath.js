include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "co.mm"
include "cdif.mm"
include "cz.mm"
include "cn.mm"
include "cr.mm"
include "wi.mm"
include "rpcn.mm"
include "ax-1.mm"
include "eqid.mm"
include "ellogdm.mm"
include "sylanbrc.mm"
include "dmlogdmgm.mm"
include "syl.mm"

theorem rpdmgm
  let cA: class A


  assert |- ( A e. RR+ -> A e. ( CC \ ( ZZ \ NN ) ) )

  proof
    cA
    crp
    wcel
    #
    cA
    cc
    cmnf
    cc0
    cioc
    co
    cdif
    #
    wcel
    #
    cA
    cc
    cz
    cn
    cdif
    cdif
    wcel
    @0
    cA
    cc
    wcel
    cA
    cr
    wcel
    #
    @0
    wi
    @2
    cA
    rpcn
    @0
    @3
    ax-1
    cA
    @1
    @1
    eqid
    ellogdm
    sylanbrc
    cA
    dmlogdmgm
    syl
end
