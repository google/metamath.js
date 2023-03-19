include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cn0.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "cr.mm"
include "crp.mm"
include "wceq.mm"
include "zre.mm"
include "nnrp.mm"
include "modval.mm"
include "syl2an.mm"
include "nnz.mm"
include "adantl.mm"
include "nndivre.mm"
include "sylan.mm"
include "flcld.mm"
include "zmulcld.mm"
include "zsubcl.mm"
include "syldan.mm"
include "eqeltrd.mm"
include "modge0.mm"
include "elnn0z.mm"
include "sylanbrc.mm"

theorem zmodcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. NN ) -> ( A mod B ) e. NN0 )

  proof
    cA
    cz
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cA
    cB
    cmo
    co
    #
    cz
    wcel
    cc0
    @3
    cle
    wbr
    #
    @3
    cn0
    wcel
    @2
    @3
    cA
    cB
    cA
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cz
    @0
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    @3
    @8
    wceq
    @1
    cA
    zre
    #
    cB
    nnrp
    #
    cA
    cB
    modval
    syl2an
    @0
    @1
    @7
    cz
    wcel
    @8
    cz
    wcel
    @2
    cB
    @6
    @1
    cB
    cz
    wcel
    @0
    cB
    nnz
    adantl
    @2
    @5
    @0
    @9
    @1
    @5
    cr
    wcel
    @11
    cA
    cB
    nndivre
    sylan
    flcld
    zmulcld
    cA
    @7
    zsubcl
    syldan
    eqeltrd
    @0
    @9
    @10
    @4
    @1
    @11
    @12
    cA
    cB
    modge0
    syl2an
    @3
    elnn0z
    sylanbrc
end
