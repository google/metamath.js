include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "addsub.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "nn0nnaddcl.mm"
include "sylan.mm"
include "eqeltrd.mm"

theorem nnaddm1cl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN /\ B e. NN ) -> ( ( A + B ) - 1 ) e. NN )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    cA
    cB
    caddc
    co
    c1
    cmin
    co
    #
    cA
    c1
    cmin
    co
    #
    cB
    caddc
    co
    #
    cn
    @0
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @2
    @4
    wceq
    #
    @1
    cA
    nncn
    cB
    nncn
    @5
    @6
    c1
    cc
    wcel
    @7
    ax-1cn
    cA
    cB
    c1
    addsub
    mp3an3
    syl2an
    @0
    @3
    cn0
    wcel
    @1
    @4
    cn
    wcel
    cA
    nnm1nn0
    @3
    cB
    nn0nnaddcl
    sylan
    eqeltrd
end
