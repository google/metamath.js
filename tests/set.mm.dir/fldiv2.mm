include "cr.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "nndivre.mm"
include "fldiv.mm"
include "stoic3.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "recn.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "divdiv1.mm"
include "syl3an.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem fldiv2
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( A e. RR /\ M e. NN /\ N e. NN ) -> ( |_ ` ( ( |_ ` ( A / M ) ) / N ) ) = ( |_ ` ( A / ( M x. N ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cA
    cM
    cdiv
    co
    #
    cfl
    cfv
    cN
    cdiv
    co
    cfl
    cfv
    #
    @4
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cA
    cM
    cN
    cmul
    co
    cdiv
    co
    #
    cfl
    cfv
    @0
    @1
    @4
    cr
    wcel
    @2
    @5
    @7
    wceq
    cA
    cM
    nndivre
    @4
    cN
    fldiv
    stoic3
    @3
    @6
    @8
    cfl
    @0
    cA
    cc
    wcel
    @1
    cM
    cc
    wcel
    #
    cM
    cc0
    wne
    #
    wa
    @2
    cN
    cc
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    @6
    @8
    wceq
    cA
    recn
    @1
    @9
    @10
    cM
    nncn
    cM
    nnne0
    jca
    @2
    @11
    @12
    cN
    nncn
    cN
    nnne0
    jca
    cA
    cM
    cN
    divdiv1
    syl3an
    fveq2d
    eqtrd
end
