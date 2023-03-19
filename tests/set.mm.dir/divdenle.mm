include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cdenom.mm"
include "cfv.mm"
include "cgcd.mm"
include "cle.mm"
include "cnumer.mm"
include "wceq.mm"
include "divnumden.mm"
include "simprd.mm"
include "c1.mm"
include "wbr.mm"
include "cc0.mm"
include "wn.mm"
include "simpl.mm"
include "nnz.mm"
include "adantl.mm"
include "nnne0.mm"
include "neneqd.mm"
include "intnand.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "nnge1d.mm"
include "cr.mm"
include "clt.mm"
include "wb.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "nnred.mm"
include "nngt0d.mm"
include "nnre.mm"
include "nngt0.mm"
include "lediv2.mm"
include "syl222anc.mm"
include "mpbid.mm"
include "cc.mm"
include "nncn.mm"
include "div1d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"

theorem divdenle
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let vx: setvar x


  assert |- ( ( A e. ZZ /\ B e. NN ) -> ( denom ` ( A / B ) ) <_ B )

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
    cdiv
    co
    #
    cdenom
    cfv
    #
    cB
    cA
    cB
    cgcd
    co
    #
    cdiv
    co
    #
    cB
    cle
    @2
    @3
    cnumer
    cfv
    cA
    @5
    cdiv
    co
    wceq
    @4
    @6
    wceq
    cA
    cB
    divnumden
    simprd
    @2
    @6
    cB
    c1
    cdiv
    co
    #
    cB
    cle
    @2
    c1
    @5
    cle
    wbr
    #
    @6
    @7
    cle
    wbr
    #
    @2
    @5
    @2
    @0
    cB
    cz
    wcel
    #
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
    @5
    cn
    wcel
    @0
    @1
    simpl
    @1
    @10
    @0
    cB
    nnz
    adantl
    @2
    @12
    @11
    @1
    @12
    wn
    @0
    @1
    cB
    cc0
    cB
    nnne0
    neneqd
    adantl
    intnand
    cA
    cB
    gcdn0cl
    syl21anc
    #
    nnge1d
    @2
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    #
    @5
    cr
    wcel
    cc0
    @5
    clt
    wbr
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    @8
    @9
    wb
    @2
    1red
    @14
    @2
    0lt1
    a1i
    @2
    @5
    @13
    nnred
    @2
    @5
    @13
    nngt0d
    @1
    @15
    @0
    cB
    nnre
    adantl
    @1
    @16
    @0
    cB
    nngt0
    adantl
    c1
    @5
    cB
    lediv2
    syl222anc
    mpbid
    @2
    cB
    @1
    cB
    cc
    wcel
    @0
    cB
    nncn
    adantl
    div1d
    breqtrd
    eqbrtrd
end
