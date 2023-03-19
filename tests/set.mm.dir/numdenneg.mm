include "cq.mm"
include "wcel.mm"
include "cneg.mm"
include "cnumer.mm"
include "cfv.mm"
include "cz.mm"
include "cdenom.mm"
include "cn.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cdiv.mm"
include "wa.mm"
include "qnegcl.mm"
include "qnumcl.mm"
include "znegcld.mm"
include "qdencl.mm"
include "nnzd.mm"
include "neggcd.mm"
include "syl2anc.mm"
include "qnumdencoprm.mm"
include "eqtrd.mm"
include "qeqnumdivden.mm"
include "negeqd.mm"
include "zcnd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divnegd.mm"
include "w3a.mm"
include "qnumdenbi.mm"
include "biimpa.mm"
include "syl32anc.mm"

theorem numdenneg
  let cQ: class Q


  assert |- ( Q e. QQ -> ( ( numer ` -u Q ) = -u ( numer ` Q ) /\ ( denom ` -u Q ) = ( denom ` Q ) ) )

  proof
    cQ
    cq
    wcel
    #
    cQ
    cneg
    #
    cq
    wcel
    #
    cQ
    cnumer
    cfv
    #
    cneg
    #
    cz
    wcel
    #
    cQ
    cdenom
    cfv
    #
    cn
    wcel
    #
    @4
    @6
    cgcd
    co
    #
    c1
    wceq
    #
    @1
    @4
    @6
    cdiv
    co
    #
    wceq
    #
    @1
    cnumer
    cfv
    @4
    wceq
    @1
    cdenom
    cfv
    @6
    wceq
    wa
    #
    cQ
    qnegcl
    @0
    @3
    cQ
    qnumcl
    #
    znegcld
    cQ
    qdencl
    #
    @0
    @8
    @3
    @6
    cgcd
    co
    #
    c1
    @0
    @3
    cz
    wcel
    @6
    cz
    wcel
    @8
    @15
    wceq
    @13
    @0
    @6
    @14
    nnzd
    @3
    @6
    neggcd
    syl2anc
    cQ
    qnumdencoprm
    eqtrd
    @0
    @1
    @3
    @6
    cdiv
    co
    #
    cneg
    @10
    @0
    cQ
    @16
    cQ
    qeqnumdivden
    negeqd
    @0
    @3
    @6
    @0
    @3
    @13
    zcnd
    @0
    @6
    @14
    nncnd
    @0
    @6
    @14
    nnne0d
    divnegd
    eqtrd
    @2
    @5
    @7
    w3a
    @9
    @11
    wa
    @12
    @1
    @4
    @6
    qnumdenbi
    biimpa
    syl32anc
end
