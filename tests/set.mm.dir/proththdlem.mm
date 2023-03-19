include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cn.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cdiv.mm"
include "w3a.mm"
include "2nn.mm"
include "a1i.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "nnmulcld.mm"
include "peano2nnd.mm"
include "cc0.mm"
include "1m1e0.mm"
include "nngt0d.mm"
include "syl5eqbr.mm"
include "1red.mm"
include "nnred.mm"
include "ltsubaddd.mm"
include "mpbid.mm"
include "cc.mm"
include "nncnd.mm"
include "pncan1.mm"
include "syl.mm"
include "oveq1d.mm"
include "cdvds.mm"
include "cz.mm"
include "2z.mm"
include "nnzd.mm"
include "3jca.mm"
include "iddvdsexp.mm"
include "syl2anc.mm"
include "dvdsmultr2.mm"
include "sylc.mm"
include "wb.mm"
include "nndivdvds.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "breq2.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "3anbi123d.mm"
include "syl5ibrcom.mm"
include "mpd.mm"

theorem proththdlem
  let wph: wff ph
  let cP: class P
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume proththd.n: |- ( ph -> N e. NN )
  assume proththd.k: |- ( ph -> K e. NN )
  assume proththd.p: |- ( ph -> P = ( ( K x. ( 2 ^ N ) ) + 1 ) )


  assert |- ( ph -> ( P e. NN /\ 1 < P /\ ( ( P - 1 ) / 2 ) e. NN ) )

  proof
    wph
    cP
    cK
    c2
    cN
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    cP
    cn
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    w3a
    #
    proththd.p
    wph
    @9
    @3
    @2
    cn
    wcel
    #
    c1
    @2
    clt
    wbr
    #
    @2
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    w3a
    wph
    @10
    @11
    @14
    wph
    @1
    wph
    cK
    @0
    proththd.k
    wph
    c2
    cN
    c2
    cn
    wcel
    #
    wph
    2nn
    a1i
    #
    wph
    cN
    proththd.n
    nnnn0d
    nnexpcld
    #
    nnmulcld
    #
    peano2nnd
    wph
    c1
    c1
    cmin
    co
    #
    @1
    clt
    wbr
    @11
    wph
    @19
    cc0
    @1
    clt
    1m1e0
    wph
    @1
    @18
    nngt0d
    syl5eqbr
    wph
    c1
    c1
    @1
    wph
    1red
    #
    @20
    wph
    @1
    @18
    nnred
    ltsubaddd
    mpbid
    wph
    @13
    @1
    c2
    cdiv
    co
    #
    cn
    wph
    @12
    @1
    c2
    cdiv
    wph
    @1
    cc
    wcel
    @12
    @1
    wceq
    wph
    @1
    @18
    nncnd
    @1
    pncan1
    syl
    oveq1d
    wph
    c2
    @1
    cdvds
    wbr
    #
    @21
    cn
    wcel
    #
    wph
    c2
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @0
    cz
    wcel
    #
    w3a
    c2
    @0
    cdvds
    wbr
    #
    @22
    wph
    @24
    @25
    @26
    @24
    wph
    2z
    a1i
    #
    wph
    cK
    proththd.k
    nnzd
    wph
    @0
    @17
    nnzd
    3jca
    wph
    @24
    cN
    cn
    wcel
    @27
    @28
    proththd.n
    c2
    cN
    iddvdsexp
    syl2anc
    c2
    cK
    @0
    dvdsmultr2
    sylc
    wph
    @1
    cn
    wcel
    @15
    @22
    @23
    wb
    @18
    @16
    @1
    c2
    nndivdvds
    syl2anc
    mpbid
    eqeltrd
    3jca
    @3
    @4
    @10
    @5
    @11
    @8
    @14
    cP
    @2
    cn
    eleq1
    cP
    @2
    c1
    clt
    breq2
    @3
    @7
    @13
    cn
    @3
    @6
    @12
    c2
    cdiv
    cP
    @2
    c1
    cmin
    oveq1
    oveq1d
    eleq1d
    3anbi123d
    syl5ibrcom
    mpd
end
