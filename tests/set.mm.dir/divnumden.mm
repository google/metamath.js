include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "wceq.mm"
include "cnumer.mm"
include "cfv.mm"
include "cdenom.mm"
include "cdvds.mm"
include "wbr.mm"
include "simpl.mm"
include "nnz.mm"
include "adantl.mm"
include "cc0.mm"
include "wn.mm"
include "nnne0.mm"
include "neneqd.mm"
include "intnand.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "gcddvds.mm"
include "sylan2.mm"
include "gcddiv.mm"
include "syl31anc.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "dividd.mm"
include "eqtr3d.mm"
include "cc.mm"
include "wne.mm"
include "zcn.mm"
include "adantr.mm"
include "nncn.mm"
include "w3a.mm"
include "divcan7.mm"
include "eqcomd.mm"
include "syl122anc.mm"
include "cq.mm"
include "wb.mm"
include "znq.mm"
include "simpld.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simprd.mm"
include "simpr.mm"
include "nndivdvds.mm"
include "syl2anc.mm"
include "qnumdenbi.mm"
include "mpbi2and.mm"

theorem divnumden
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let vx: setvar x


  assert |- ( ( A e. ZZ /\ B e. NN ) -> ( ( numer ` ( A / B ) ) = ( A / ( A gcd B ) ) /\ ( denom ` ( A / B ) ) = ( B / ( A gcd B ) ) ) )

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
    cA
    cB
    cgcd
    co
    #
    cdiv
    co
    #
    cB
    @3
    cdiv
    co
    #
    cgcd
    co
    #
    c1
    wceq
    #
    cA
    cB
    cdiv
    co
    #
    @4
    @5
    cdiv
    co
    #
    wceq
    #
    @8
    cnumer
    cfv
    @4
    wceq
    @8
    cdenom
    cfv
    @5
    wceq
    wa
    #
    @2
    @3
    @3
    cdiv
    co
    #
    @6
    c1
    @2
    @0
    cB
    cz
    wcel
    #
    @3
    cn
    wcel
    #
    @3
    cA
    cdvds
    wbr
    #
    @3
    cB
    cdvds
    wbr
    #
    wa
    #
    @12
    @6
    wceq
    @0
    @1
    simpl
    #
    @1
    @13
    @0
    cB
    nnz
    #
    adantl
    #
    @2
    @0
    @13
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wa
    wn
    @14
    @18
    @20
    @2
    @22
    @21
    @1
    @22
    wn
    @0
    @1
    cB
    cc0
    cB
    nnne0
    #
    neneqd
    adantl
    intnand
    cA
    cB
    gcdn0cl
    syl21anc
    #
    @1
    @0
    @13
    @17
    @19
    cA
    cB
    gcddvds
    sylan2
    #
    cA
    cB
    @3
    gcddiv
    syl31anc
    @2
    @3
    @2
    @3
    @24
    nncnd
    #
    @2
    @3
    @24
    nnne0d
    #
    dividd
    eqtr3d
    @2
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    #
    @10
    @0
    @28
    @1
    cA
    zcn
    adantr
    @1
    @29
    @0
    cB
    nncn
    adantl
    @1
    @30
    @0
    @23
    adantl
    @26
    @27
    @28
    @29
    @30
    wa
    @31
    @32
    wa
    w3a
    @9
    @8
    cA
    cB
    @3
    divcan7
    eqcomd
    syl122anc
    @2
    @8
    cq
    wcel
    @4
    cz
    wcel
    #
    @5
    cn
    wcel
    #
    @7
    @10
    wa
    @11
    wb
    cA
    cB
    znq
    @2
    @15
    @33
    @2
    @15
    @16
    @25
    simpld
    @2
    @3
    cz
    wcel
    #
    @32
    @0
    @15
    @33
    wb
    @1
    @0
    @13
    @35
    @19
    @0
    @13
    wa
    @3
    cA
    cB
    gcdcl
    nn0zd
    sylan2
    @27
    @18
    @3
    cA
    dvdsval2
    syl3anc
    mpbid
    @2
    @16
    @34
    @2
    @15
    @16
    @25
    simprd
    @2
    @1
    @14
    @16
    @34
    wb
    @0
    @1
    simpr
    @24
    cB
    @3
    nndivdvds
    syl2anc
    mpbid
    @8
    @4
    @5
    qnumdenbi
    syl3anc
    mpbi2and
end
