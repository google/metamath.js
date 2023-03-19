include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cno.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "csm.mm"
include "cabs.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "cr.mm"
include "normcl.mm"
include "adantr.mm"
include "cc0.mm"
include "normne0.mm"
include "biimpar.mm"
include "rereccld.mm"
include "recnd.mm"
include "simpl.mm"
include "norm-iii.mm"
include "syl2anc.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "normgt0.mm"
include "biimpa.mm"
include "1re.mm"
include "0le1.mm"
include "divge0.mm"
include "mpanl12.mm"
include "absidd.mm"
include "oveq1d.mm"
include "recid2d.mm"
include "3eqtrd.mm"

theorem norm1
  let cA: class A


  assert |- ( ( A e. ~H /\ A =/= 0h ) -> ( normh ` ( ( 1 / ( normh ` A ) ) .h A ) ) = 1 )

  proof
    cA
    chil
    wcel
    #
    cA
    c0v
    wne
    #
    wa
    #
    c1
    cA
    cno
    cfv
    #
    cdiv
    co
    #
    cA
    csm
    co
    cno
    cfv
    #
    @4
    cabs
    cfv
    #
    @3
    cmul
    co
    #
    @4
    @3
    cmul
    co
    c1
    @2
    @4
    cc
    wcel
    @0
    @5
    @7
    wceq
    @2
    @4
    @2
    @3
    @0
    @3
    cr
    wcel
    #
    @1
    cA
    normcl
    #
    adantr
    #
    @0
    @3
    cc0
    wne
    @1
    cA
    normne0
    biimpar
    #
    rereccld
    #
    recnd
    @0
    @1
    simpl
    @4
    cA
    norm-iii
    syl2anc
    @2
    @6
    @4
    @3
    cmul
    @2
    @4
    @12
    @2
    @8
    cc0
    @3
    clt
    wbr
    #
    cc0
    @4
    cle
    wbr
    #
    @10
    @0
    @1
    @13
    cA
    normgt0
    biimpa
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @8
    @13
    wa
    @14
    1re
    0le1
    c1
    @3
    divge0
    mpanl12
    syl2anc
    absidd
    oveq1d
    @2
    @3
    @0
    @3
    cc
    wcel
    @1
    @0
    @3
    @9
    recnd
    adantr
    @11
    recid2d
    3eqtrd
end
