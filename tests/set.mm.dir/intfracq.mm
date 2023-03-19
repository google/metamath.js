include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "caddc.mm"
include "wceq.mm"
include "clt.mm"
include "cr.mm"
include "w3a.mm"
include "zre.mm"
include "adantr.mm"
include "nnre.mm"
include "adantl.mm"
include "wne.mm"
include "nnne0.mm"
include "redivcld.mm"
include "intfrac2.mm"
include "syl.mm"
include "simp1d.mm"
include "cmul.mm"
include "cfl.mm"
include "cfv.mm"
include "fraclt1.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "a1i.mm"
include "nncn.mm"
include "dividd.mm"
include "3brtr4d.mm"
include "wb.mm"
include "reflcl.mm"
include "syl5eqel.mm"
include "resubcld.mm"
include "nngt0.mm"
include "jca.mm"
include "ltmuldiv2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "cc.mm"
include "recnd.mm"
include "flcld.mm"
include "zcnd.mm"
include "subdid.mm"
include "syl5eq.mm"
include "zcn.mm"
include "divcan2d.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "nnz.mm"
include "zmulcld.mm"
include "zsubcld.mm"
include "zltlem1.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "peano2rem.mm"
include "lemuldiv2.mm"
include "simp3d.mm"
include "3jca.mm"

theorem intfracq
  let cF: class F
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume intfracq.1: |- Z = ( |_ ` ( M / N ) )
  assume intfracq.2: |- F = ( ( M / N ) - Z )


  assert |- ( ( M e. ZZ /\ N e. NN ) -> ( 0 <_ F /\ F <_ ( ( N - 1 ) / N ) /\ ( M / N ) = ( Z + F ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cc0
    cF
    cle
    wbr
    #
    cF
    cN
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    cle
    wbr
    #
    cM
    cN
    cdiv
    co
    #
    cZ
    cF
    caddc
    co
    wceq
    #
    @2
    @3
    cF
    c1
    clt
    wbr
    #
    @7
    @2
    @6
    cr
    wcel
    #
    @3
    @8
    @7
    w3a
    @2
    cM
    cN
    @0
    cM
    cr
    wcel
    @1
    cM
    zre
    adantr
    @1
    cN
    cr
    wcel
    #
    @0
    cN
    nnre
    #
    adantl
    #
    @1
    cN
    cc0
    wne
    @0
    cN
    nnne0
    #
    adantl
    #
    redivcld
    #
    @6
    cF
    cZ
    intfracq.1
    intfracq.2
    intfrac2
    syl
    #
    simp1d
    @2
    cN
    cF
    cmul
    co
    #
    @4
    cle
    wbr
    #
    @5
    @2
    @17
    cN
    clt
    wbr
    #
    @18
    @2
    @19
    cF
    cN
    cN
    cdiv
    co
    #
    clt
    wbr
    #
    @2
    @6
    @6
    cfl
    cfv
    #
    cmin
    co
    #
    c1
    cF
    @20
    clt
    @2
    @9
    @23
    c1
    clt
    wbr
    @15
    @6
    fraclt1
    syl
    cF
    @23
    wceq
    @2
    cF
    @6
    cZ
    cmin
    co
    #
    @23
    intfracq.2
    cZ
    @22
    @6
    cmin
    intfracq.1
    oveq2i
    eqtri
    a1i
    @1
    @20
    c1
    wceq
    @0
    @1
    cN
    cN
    nncn
    #
    @13
    dividd
    adantl
    3brtr4d
    @2
    cF
    cr
    wcel
    #
    @10
    @10
    cc0
    cN
    clt
    wbr
    #
    wa
    #
    @19
    @21
    wb
    @2
    cF
    @24
    cr
    intfracq.2
    @2
    @6
    cZ
    @15
    @2
    cZ
    @22
    cr
    intfracq.1
    @2
    @9
    @22
    cr
    wcel
    @15
    @6
    reflcl
    syl
    syl5eqel
    resubcld
    syl5eqel
    #
    @12
    @1
    @28
    @0
    @1
    @10
    @27
    @11
    cN
    nngt0
    jca
    adantl
    #
    cF
    cN
    cN
    ltmuldiv2
    syl3anc
    mpbird
    @2
    @17
    cz
    wcel
    cN
    cz
    wcel
    #
    @19
    @18
    wb
    @2
    @17
    cN
    @6
    cmul
    co
    #
    cN
    cZ
    cmul
    co
    #
    cmin
    co
    #
    cz
    @2
    @17
    cN
    @24
    cmul
    co
    @34
    cF
    @24
    cN
    cmul
    intfracq.2
    oveq2i
    @2
    cN
    @6
    cZ
    @1
    cN
    cc
    wcel
    @0
    @25
    adantl
    #
    @2
    @6
    @15
    recnd
    @2
    cZ
    @2
    cZ
    @22
    cz
    intfracq.1
    @2
    @6
    @15
    flcld
    syl5eqel
    #
    zcnd
    subdid
    syl5eq
    @2
    @32
    @33
    @2
    @32
    cM
    cz
    @2
    cM
    cN
    @0
    cM
    cc
    wcel
    @1
    cM
    zcn
    adantr
    @35
    @14
    divcan2d
    @0
    @1
    simpl
    eqeltrd
    @2
    cN
    cZ
    @1
    @31
    @0
    cN
    nnz
    adantl
    #
    @36
    zmulcld
    zsubcld
    eqeltrd
    @37
    @17
    cN
    zltlem1
    syl2anc
    mpbid
    @2
    @26
    @4
    cr
    wcel
    #
    @28
    @18
    @5
    wb
    @29
    @1
    @38
    @0
    @1
    @10
    @38
    @11
    cN
    peano2rem
    syl
    adantl
    @30
    cF
    @4
    cN
    lemuldiv2
    syl3anc
    mpbid
    @2
    @3
    @8
    @7
    @16
    simp3d
    3jca
end
