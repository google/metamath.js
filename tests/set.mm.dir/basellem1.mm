include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "cpi.mm"
include "cmul.mm"
include "cdiv.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cioo.mm"
include "crp.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "pirp.mm"
include "rpmulcl.mm"
include "sylancl.mm"
include "caddc.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "mpan.mm"
include "peano2nnd.mm"
include "syl5eqel.mm"
include "rpdivcl.mm"
include "syl2anr.mm"
include "rpred.mm"
include "rpgt0d.mm"
include "adantl.mm"
include "nnred.mm"
include "adantr.mm"
include "syl5eqelr.mm"
include "cle.mm"
include "cc.mm"
include "wceq.mm"
include "nncnd.mm"
include "2cn.mm"
include "mulcom.mm"
include "elfzle2.mm"
include "wb.mm"
include "nnre.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "lemul2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "syl6breqr.mm"
include "nngt0d.mm"
include "pire.mm"
include "remulcl.mm"
include "ltdiv2.mm"
include "syl222anc.mm"
include "wne.mm"
include "picn.mm"
include "2cnne0.mm"
include "nnne0d.mm"
include "divcan5.mm"
include "syl112anc.mm"
include "breqtrd.mm"
include "cxr.mm"
include "w3a.mm"
include "0xr.mm"
include "rehalfcl.mm"
include "rexr.mm"
include "mp2b.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"

theorem basellem1
  let cK: class K
  let cM: class M
  let cN: class N
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vt: setvar t
  let cA: class A
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cT: class T
  assume basel.n: |- N = ( ( 2 x. M ) + 1 )


  assert |- ( ( M e. NN /\ K e. ( 1 ... M ) ) -> ( ( K x. _pi ) / N ) e. ( 0 (,) ( _pi / 2 ) ) )

  proof
    cM
    cn
    wcel
    #
    cK
    c1
    cM
    cfz
    co
    wcel
    #
    wa
    #
    cK
    cpi
    cmul
    co
    #
    cN
    cdiv
    co
    #
    cr
    wcel
    #
    cc0
    @4
    clt
    wbr
    #
    @4
    cpi
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @4
    cc0
    @7
    cioo
    co
    wcel
    #
    @2
    @4
    @1
    @3
    crp
    wcel
    #
    cN
    crp
    wcel
    @4
    crp
    wcel
    @0
    @1
    cK
    crp
    wcel
    cpi
    crp
    wcel
    @10
    @1
    cK
    cK
    cM
    elfznn
    #
    nnrpd
    pirp
    cK
    cpi
    rpmulcl
    sylancl
    #
    @0
    cN
    @0
    cN
    c2
    cM
    cmul
    co
    #
    c1
    caddc
    co
    #
    cn
    basel.n
    @0
    @13
    c2
    cn
    wcel
    #
    @0
    @13
    cn
    wcel
    #
    2nn
    c2
    cM
    nnmulcl
    mpan
    #
    peano2nnd
    syl5eqel
    #
    nnrpd
    @3
    cN
    rpdivcl
    syl2anr
    #
    rpred
    @2
    @4
    @19
    rpgt0d
    @2
    @4
    @3
    cK
    c2
    cmul
    co
    #
    cdiv
    co
    #
    @7
    clt
    @2
    @20
    cN
    clt
    wbr
    #
    @4
    @21
    clt
    wbr
    #
    @2
    @20
    @14
    cN
    clt
    @2
    @20
    @13
    @14
    @2
    @20
    @2
    cK
    cn
    wcel
    #
    @15
    @20
    cn
    wcel
    @1
    @24
    @0
    @11
    adantl
    #
    2nn
    cK
    c2
    nnmulcl
    sylancl
    #
    nnred
    #
    @2
    @13
    @0
    @16
    @1
    @17
    adantr
    nnred
    #
    @2
    @14
    cN
    cr
    basel.n
    @2
    cN
    @0
    cN
    cn
    wcel
    @1
    @18
    adantr
    #
    nnred
    #
    syl5eqelr
    @2
    @20
    c2
    cK
    cmul
    co
    #
    @13
    cle
    @2
    cK
    cc
    wcel
    #
    c2
    cc
    wcel
    #
    @20
    @31
    wceq
    @2
    cK
    @25
    nncnd
    #
    2cn
    cK
    c2
    mulcom
    sylancl
    @2
    cK
    cM
    cle
    wbr
    #
    @31
    @13
    cle
    wbr
    #
    @1
    @35
    @0
    cK
    c1
    cM
    elfzle2
    adantl
    @2
    cK
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @35
    @36
    wb
    @2
    cK
    @25
    nnred
    #
    @0
    @38
    @1
    cM
    nnre
    adantr
    @41
    @2
    @39
    @40
    2re
    2pos
    pm3.2i
    a1i
    cK
    cM
    c2
    lemul2
    syl3anc
    mpbid
    eqbrtrd
    @2
    @13
    @28
    ltp1d
    lelttrd
    basel.n
    syl6breqr
    @2
    @20
    cr
    wcel
    cc0
    @20
    clt
    wbr
    cN
    cr
    wcel
    cc0
    cN
    clt
    wbr
    @3
    cr
    wcel
    #
    cc0
    @3
    clt
    wbr
    @22
    @23
    wb
    @27
    @2
    @20
    @26
    nngt0d
    @30
    @2
    cN
    @29
    nngt0d
    @2
    @37
    cpi
    cr
    wcel
    #
    @43
    @42
    pire
    cK
    cpi
    remulcl
    sylancl
    @2
    @3
    @1
    @10
    @0
    @12
    adantl
    rpgt0d
    @20
    cN
    @3
    ltdiv2
    syl222anc
    mpbid
    @2
    cpi
    cc
    wcel
    #
    @33
    c2
    cc0
    wne
    wa
    #
    @32
    cK
    cc0
    wne
    @21
    @7
    wceq
    @45
    @2
    picn
    a1i
    @46
    @2
    2cnne0
    a1i
    @34
    @2
    cK
    @25
    nnne0d
    cpi
    c2
    cK
    divcan5
    syl112anc
    breqtrd
    cc0
    cxr
    wcel
    @7
    cxr
    wcel
    #
    @9
    @5
    @6
    @8
    w3a
    wb
    0xr
    @44
    @7
    cr
    wcel
    @47
    pire
    cpi
    rehalfcl
    @7
    rexr
    mp2b
    cc0
    @7
    @4
    elioo2
    mp2an
    syl3anbrc
end
