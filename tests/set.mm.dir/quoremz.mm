include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cr.mm"
include "zre.mm"
include "adantr.mm"
include "nnre.mm"
include "adantl.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "redivcld.mm"
include "flcld.mm"
include "syl5eqel.mm"
include "cmin.mm"
include "cle.mm"
include "zcnd.mm"
include "cc.mm"
include "nncn.mm"
include "divcan3d.mm"
include "flle.mm"
include "syl.mm"
include "syl5eqbr.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "nnz.mm"
include "zmulcld.mm"
include "zred.mm"
include "nngt0.mm"
include "lediv1.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "simpl.mm"
include "znn0sub.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "c1.mm"
include "oveq2i.mm"
include "fraclt1.mm"
include "oveq1i.mm"
include "zcn.mm"
include "jca.mm"
include "divsubdir.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "dividd.mm"
include "3brtr4d.mm"
include "nn0red.mm"
include "ltdiv1.mm"
include "pncan3d.mm"
include "syl5req.mm"
include "jca31.mm"

theorem quoremz
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  assume quorem.1: |- Q = ( |_ ` ( A / B ) )
  assume quorem.2: |- R = ( A - ( B x. Q ) )


  assert |- ( ( A e. ZZ /\ B e. NN ) -> ( ( Q e. ZZ /\ R e. NN0 ) /\ ( R < B /\ A = ( ( B x. Q ) + R ) ) ) )

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
    cQ
    cz
    wcel
    cR
    cn0
    wcel
    cR
    cB
    clt
    wbr
    #
    cA
    cB
    cQ
    cmul
    co
    #
    cR
    caddc
    co
    #
    wceq
    #
    wa
    @2
    cQ
    cA
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    cz
    quorem.1
    @2
    @7
    @2
    cA
    cB
    @0
    cA
    cr
    wcel
    #
    @1
    cA
    zre
    adantr
    #
    @1
    cB
    cr
    wcel
    #
    @0
    cB
    nnre
    adantl
    #
    @1
    cB
    cc0
    wne
    #
    @0
    cB
    nnne0
    #
    adantl
    #
    redivcld
    #
    flcld
    syl5eqel
    #
    @2
    cR
    cA
    @4
    cmin
    co
    #
    cn0
    quorem.2
    @2
    @4
    cA
    cle
    wbr
    #
    @18
    cn0
    wcel
    #
    @2
    @19
    @4
    cB
    cdiv
    co
    #
    @7
    cle
    wbr
    #
    @2
    @21
    cQ
    @7
    cle
    @2
    cQ
    cB
    @2
    cQ
    @17
    zcnd
    @1
    cB
    cc
    wcel
    #
    @0
    cB
    nncn
    #
    adantl
    @15
    divcan3d
    #
    @2
    cQ
    @8
    @7
    cle
    quorem.1
    @2
    @7
    cr
    wcel
    #
    @8
    @7
    cle
    wbr
    @16
    @7
    flle
    syl
    syl5eqbr
    eqbrtrd
    @2
    @4
    cr
    wcel
    @9
    @11
    cc0
    cB
    clt
    wbr
    #
    @19
    @22
    wb
    @2
    @4
    @2
    cB
    cQ
    @1
    cB
    cz
    wcel
    @0
    cB
    nnz
    adantl
    @17
    zmulcld
    #
    zred
    @10
    @12
    @1
    @27
    @0
    cB
    nngt0
    adantl
    #
    @4
    cA
    cB
    lediv1
    syl112anc
    mpbird
    @2
    @4
    cz
    wcel
    @0
    @19
    @20
    wb
    @28
    @0
    @1
    simpl
    @4
    cA
    znn0sub
    syl2anc
    mpbid
    syl5eqel
    #
    @2
    @3
    @6
    @2
    @3
    cR
    cB
    cdiv
    co
    #
    cB
    cB
    cdiv
    co
    #
    clt
    wbr
    #
    @2
    @7
    cQ
    cmin
    co
    #
    c1
    @31
    @32
    clt
    @2
    @34
    @7
    @8
    cmin
    co
    #
    c1
    clt
    cQ
    @8
    @7
    cmin
    quorem.1
    oveq2i
    @2
    @26
    @35
    c1
    clt
    wbr
    @16
    @7
    fraclt1
    syl
    syl5eqbr
    @2
    @31
    @18
    cB
    cdiv
    co
    #
    @34
    cR
    @18
    cB
    cdiv
    quorem.2
    oveq1i
    @2
    @36
    @7
    @21
    cmin
    co
    #
    @34
    @2
    cA
    cc
    wcel
    #
    @4
    cc
    wcel
    @23
    @13
    wa
    #
    @36
    @37
    wceq
    @0
    @38
    @1
    cA
    zcn
    adantr
    #
    @2
    @4
    @28
    zcnd
    #
    @1
    @39
    @0
    @1
    @23
    @13
    @24
    @14
    jca
    adantl
    cA
    @4
    cB
    divsubdir
    syl3anc
    @2
    @21
    cQ
    @7
    cmin
    @25
    oveq2d
    eqtrd
    syl5eq
    @1
    @32
    c1
    wceq
    @0
    @1
    cB
    @24
    @14
    dividd
    adantl
    3brtr4d
    @2
    cR
    cr
    wcel
    @11
    @11
    @27
    @3
    @33
    wb
    @2
    cR
    @30
    nn0red
    @12
    @12
    @29
    cR
    cB
    cB
    ltdiv1
    syl112anc
    mpbird
    @2
    @5
    @4
    @18
    caddc
    co
    cA
    cR
    @18
    @4
    caddc
    quorem.2
    oveq2i
    @2
    @4
    cA
    @41
    @40
    pncan3d
    syl5req
    jca
    jca31
end
