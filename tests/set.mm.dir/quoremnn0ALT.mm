include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "fldivnn0.mm"
include "syl5eqel.mm"
include "cmin.mm"
include "cle.mm"
include "nnnn0.mm"
include "adantl.mm"
include "nn0mulcld.mm"
include "simpl.mm"
include "nn0cnd.mm"
include "cc.mm"
include "nncn.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divcan3d.mm"
include "cr.mm"
include "nn0nndivcl.mm"
include "flle.mm"
include "syl.mm"
include "syl5eqbr.mm"
include "eqbrtrd.mm"
include "wb.mm"
include "nn0red.mm"
include "nn0re.mm"
include "adantr.mm"
include "nnre.mm"
include "nngt0.mm"
include "lediv1.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "nn0sub2.mm"
include "syl3anc.mm"
include "c1.mm"
include "oveq2i.mm"
include "fraclt1.mm"
include "oveq1i.mm"
include "nn0cn.mm"
include "jca.mm"
include "divsubdir.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "dividd.mm"
include "3brtr4d.mm"
include "ltdiv1.mm"
include "pncan3d.mm"
include "syl5req.mm"
include "jca31.mm"

theorem quoremnn0ALT
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  assume quorem.1: |- Q = ( |_ ` ( A / B ) )
  assume quorem.2: |- R = ( A - ( B x. Q ) )


  assert |- ( ( A e. NN0 /\ B e. NN ) -> ( ( Q e. NN0 /\ R e. NN0 ) /\ ( R < B /\ A = ( ( B x. Q ) + R ) ) ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cQ
    cn0
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
    cn0
    quorem.1
    cA
    cB
    fldivnn0
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
    cn0
    wcel
    @0
    @4
    cA
    cle
    wbr
    #
    @10
    cn0
    wcel
    @2
    cB
    cQ
    @1
    cB
    cn0
    wcel
    @0
    cB
    nnnn0
    adantl
    @9
    nn0mulcld
    #
    @0
    @1
    simpl
    @2
    @11
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
    @13
    cQ
    @7
    cle
    @2
    cQ
    cB
    @2
    cQ
    @9
    nn0cnd
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
    cA
    cB
    nn0nndivcl
    #
    @7
    flle
    syl
    syl5eqbr
    eqbrtrd
    @2
    @4
    cr
    wcel
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    @11
    @14
    wb
    @2
    @4
    @12
    nn0red
    @0
    @22
    @1
    cA
    nn0re
    adantr
    @1
    @23
    @0
    cB
    nnre
    adantl
    #
    @1
    @24
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
    @4
    cA
    nn0sub2
    syl3anc
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
    @28
    @29
    clt
    @2
    @31
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
    @20
    @32
    c1
    clt
    wbr
    @21
    @7
    fraclt1
    syl
    syl5eqbr
    @2
    @28
    @10
    cB
    cdiv
    co
    #
    @31
    cR
    @10
    cB
    cdiv
    quorem.2
    oveq1i
    @2
    @33
    @7
    @13
    cmin
    co
    #
    @31
    @2
    cA
    cc
    wcel
    #
    @4
    cc
    wcel
    @15
    @17
    wa
    #
    @33
    @34
    wceq
    @0
    @35
    @1
    cA
    nn0cn
    adantr
    #
    @2
    @4
    @12
    nn0cnd
    #
    @1
    @36
    @0
    @1
    @15
    @17
    @16
    @18
    jca
    adantl
    cA
    @4
    cB
    divsubdir
    syl3anc
    @2
    @13
    cQ
    @7
    cmin
    @19
    oveq2d
    eqtrd
    syl5eq
    @1
    @29
    c1
    wceq
    @0
    @1
    cB
    @16
    @18
    dividd
    adantl
    3brtr4d
    @2
    cR
    cr
    wcel
    @23
    @23
    @24
    @3
    @30
    wb
    @2
    cR
    @27
    nn0red
    @25
    @25
    @26
    cR
    cB
    cB
    ltdiv1
    syl112anc
    mpbird
    @2
    @5
    @4
    @10
    caddc
    co
    cA
    cR
    @10
    @4
    caddc
    quorem.2
    oveq2i
    @2
    @4
    cA
    @38
    @37
    pncan3d
    syl5req
    jca
    jca31
end
