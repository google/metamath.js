include "cc.mm"
include "wcel.mm"
include "crp.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crli.mm"
include "wbr.mm"
include "clt.mm"
include "cabs.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "abscl.mm"
include "rerpdivcl.mm"
include "sylan.mm"
include "simpll.mm"
include "rpcn.mm"
include "ad2antrl.mm"
include "wne.mm"
include "rpne0.mm"
include "absdivd.mm"
include "rpre.mm"
include "cle.mm"
include "rpge0.mm"
include "absidd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "simprr.mm"
include "wb.mm"
include "abscld.mm"
include "ad2antlr.mm"
include "rpgt0.mm"
include "ltdiv23.mm"
include "syl122anc.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "simpl.mm"
include "adantl.mm"
include "divcld.mm"
include "wss.mm"
include "rpssre.mm"
include "a1i.mm"
include "rlim0lt.mm"
include "mpbird.mm"

theorem divrcnv
  let cA: class A
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y

  disjoint A n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A e. CC -> ( n e. RR+ |-> ( A / n ) ) ~~>r 0 )

  proof
    cA
    cc
    wcel
    #
    vn
    crp
    cA
    vn
    cv
    #
    cdiv
    co
    #
    cmpt
    cc0
    crli
    wbr
    vy
    cv
    #
    @1
    clt
    wbr
    #
    @2
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vn
    crp
    wral
    #
    vy
    cr
    wrex
    #
    vx
    crp
    wral
    @0
    @10
    vx
    crp
    @0
    @6
    crp
    wcel
    #
    wa
    #
    cA
    cabs
    cfv
    #
    @6
    cdiv
    co
    #
    cr
    wcel
    #
    @14
    @1
    clt
    wbr
    #
    @7
    wi
    #
    vn
    crp
    wral
    #
    @10
    @0
    @13
    cr
    wcel
    #
    @11
    @15
    cA
    abscl
    @13
    @6
    rerpdivcl
    sylan
    @12
    @17
    vn
    crp
    @12
    @1
    crp
    wcel
    #
    @16
    @7
    @12
    @20
    @16
    wa
    #
    wa
    #
    @5
    @13
    @1
    cdiv
    co
    #
    @6
    clt
    @22
    @5
    @13
    @1
    cabs
    cfv
    #
    cdiv
    co
    @23
    @22
    cA
    @1
    @0
    @11
    @21
    simpll
    #
    @20
    @1
    cc
    wcel
    #
    @12
    @16
    @1
    rpcn
    #
    ad2antrl
    @20
    @1
    cc0
    wne
    #
    @12
    @16
    @1
    rpne0
    #
    ad2antrl
    absdivd
    @22
    @24
    @1
    @13
    cdiv
    @22
    @1
    @20
    @1
    cr
    wcel
    #
    @12
    @16
    @1
    rpre
    ad2antrl
    #
    @20
    cc0
    @1
    cle
    wbr
    @12
    @16
    @1
    rpge0
    ad2antrl
    absidd
    oveq2d
    eqtrd
    @22
    @16
    @23
    @6
    clt
    wbr
    #
    @12
    @20
    @16
    simprr
    @22
    @19
    @6
    cr
    wcel
    #
    cc0
    @6
    clt
    wbr
    #
    @30
    cc0
    @1
    clt
    wbr
    #
    @16
    @32
    wb
    @22
    cA
    @25
    abscld
    @11
    @33
    @0
    @21
    @6
    rpre
    ad2antlr
    @11
    @34
    @0
    @21
    @6
    rpgt0
    ad2antlr
    @31
    @20
    @35
    @12
    @16
    @1
    rpgt0
    ad2antrl
    @13
    @6
    @1
    ltdiv23
    syl122anc
    mpbid
    eqbrtrd
    expr
    ralrimiva
    @9
    @18
    vy
    @14
    cr
    @3
    @14
    wceq
    #
    @8
    @17
    vn
    crp
    @36
    @4
    @16
    @7
    @3
    @14
    @1
    clt
    breq1
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimiva
    @0
    vx
    vy
    vn
    crp
    @2
    @0
    @2
    cc
    wcel
    vn
    crp
    @0
    @20
    wa
    cA
    @1
    @0
    @20
    simpl
    @20
    @26
    @0
    @27
    adantl
    @20
    @28
    @0
    @29
    adantl
    divcld
    ralrimiva
    crp
    cr
    wss
    @0
    rpssre
    a1i
    rlim0lt
    mpbird
end
