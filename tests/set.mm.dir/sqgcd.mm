include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cmul.mm"
include "gcdnncl.mm"
include "nnsqcld.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "cdiv.mm"
include "wceq.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "nnsqcl.mm"
include "nnzd.mm"
include "adantr.mm"
include "adantl.mm"
include "nnz.mm"
include "gcddvds.mm"
include "syl2an.mm"
include "simpld.mm"
include "wi.mm"
include "dvdssqim.mm"
include "syl2anc.mm"
include "mpd.mm"
include "simprd.mm"
include "gcddiv.mm"
include "syl32anc.mm"
include "cc.mm"
include "nncn.mm"
include "nnne0d.mm"
include "sqdivd.mm"
include "oveq12d.mm"
include "syl31anc.mm"
include "dividd.mm"
include "eqtr3d.mm"
include "cc0.mm"
include "clt.mm"
include "wne.mm"
include "wb.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "cr.mm"
include "nnre.mm"
include "nnred.mm"
include "nngt0.mm"
include "nngt0d.mm"
include "divgt0d.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "2nn.mm"
include "rppwr.mm"
include "mp3an3.mm"
include "3eqtr2d.mm"
include "wn.mm"
include "anim12i.mm"
include "neneqd.mm"
include "intnanrd.mm"
include "gcdn0cl.mm"
include "ax-1cn.mm"
include "divmul.mm"
include "mp3an2.mm"
include "syl12anc.mm"

theorem sqgcd
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ N e. NN ) -> ( ( M gcd N ) ^ 2 ) = ( ( M ^ 2 ) gcd ( N ^ 2 ) ) )

  proof
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cM
    cN
    cgcd
    co
    #
    c2
    cexp
    co
    #
    c1
    cmul
    co
    #
    @4
    cM
    c2
    cexp
    co
    #
    cN
    c2
    cexp
    co
    #
    cgcd
    co
    #
    @2
    @4
    @2
    @4
    @2
    @3
    cM
    cN
    gcdnncl
    #
    nnsqcld
    #
    nncnd
    #
    mulid1d
    @2
    @8
    @4
    cdiv
    co
    #
    c1
    wceq
    #
    @5
    @8
    wceq
    #
    @2
    @12
    @6
    @4
    cdiv
    co
    #
    @7
    @4
    cdiv
    co
    #
    cgcd
    co
    #
    cM
    @3
    cdiv
    co
    #
    c2
    cexp
    co
    #
    cN
    @3
    cdiv
    co
    #
    c2
    cexp
    co
    #
    cgcd
    co
    #
    c1
    @2
    @6
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    @4
    cn
    wcel
    @4
    @6
    cdvds
    wbr
    #
    @4
    @7
    cdvds
    wbr
    #
    @12
    @17
    wceq
    @0
    @23
    @1
    @0
    @6
    cM
    nnsqcl
    #
    nnzd
    #
    adantr
    @1
    @24
    @0
    @1
    @7
    cN
    nnsqcl
    nnzd
    #
    adantl
    @10
    @2
    @3
    cM
    cdvds
    wbr
    #
    @25
    @2
    @30
    @3
    cN
    cdvds
    wbr
    #
    @0
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @30
    @31
    wa
    #
    @1
    cM
    nnz
    #
    cN
    nnz
    #
    cM
    cN
    gcddvds
    syl2an
    #
    simpld
    #
    @2
    @3
    cz
    wcel
    #
    @32
    @30
    @25
    wi
    @2
    @3
    @9
    nnzd
    #
    @0
    @32
    @1
    @35
    adantr
    #
    @3
    cM
    dvdssqim
    syl2anc
    mpd
    @2
    @31
    @26
    @2
    @30
    @31
    @37
    simprd
    #
    @2
    @39
    @33
    @31
    @26
    wi
    @40
    @1
    @33
    @0
    @36
    adantl
    #
    @3
    cN
    dvdssqim
    syl2anc
    mpd
    @6
    @7
    @4
    gcddiv
    syl32anc
    @2
    @19
    @15
    @21
    @16
    cgcd
    @2
    cM
    @3
    @0
    cM
    cc
    wcel
    @1
    cM
    nncn
    adantr
    @2
    @3
    @9
    nncnd
    #
    @2
    @3
    @9
    nnne0d
    #
    sqdivd
    @2
    cN
    @3
    @1
    cN
    cc
    wcel
    @0
    cN
    nncn
    adantl
    @44
    @45
    sqdivd
    oveq12d
    @2
    @18
    @20
    cgcd
    co
    #
    c1
    wceq
    #
    @22
    c1
    wceq
    #
    @2
    @3
    @3
    cdiv
    co
    #
    @46
    c1
    @2
    @32
    @33
    @3
    cn
    wcel
    @34
    @49
    @46
    wceq
    @41
    @43
    @9
    @37
    cM
    cN
    @3
    gcddiv
    syl31anc
    @2
    @3
    @44
    @45
    dividd
    eqtr3d
    @2
    @18
    cn
    wcel
    #
    @20
    cn
    wcel
    #
    @47
    @48
    wi
    #
    @2
    @18
    cz
    wcel
    #
    cc0
    @18
    clt
    wbr
    @50
    @2
    @30
    @53
    @38
    @2
    @39
    @3
    cc0
    wne
    #
    @32
    @30
    @53
    wb
    @40
    @45
    @41
    @3
    cM
    dvdsval2
    syl3anc
    mpbid
    @2
    cM
    @3
    @0
    cM
    cr
    wcel
    @1
    cM
    nnre
    adantr
    @2
    @3
    @9
    nnred
    #
    @0
    cc0
    cM
    clt
    wbr
    @1
    cM
    nngt0
    adantr
    @2
    @3
    @9
    nngt0d
    #
    divgt0d
    @18
    elnnz
    sylanbrc
    @2
    @20
    cz
    wcel
    #
    cc0
    @20
    clt
    wbr
    @51
    @2
    @31
    @57
    @42
    @2
    @39
    @54
    @33
    @31
    @57
    wb
    @40
    @45
    @43
    @3
    cN
    dvdsval2
    syl3anc
    mpbid
    @2
    cN
    @3
    @1
    cN
    cr
    wcel
    @0
    cN
    nnre
    adantl
    @55
    @1
    cc0
    cN
    clt
    wbr
    @0
    cN
    nngt0
    adantl
    @56
    divgt0d
    @20
    elnnz
    sylanbrc
    @50
    @51
    c2
    cn
    wcel
    @52
    2nn
    @18
    @20
    c2
    rppwr
    mp3an3
    syl2anc
    mpd
    3eqtr2d
    @2
    @8
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @4
    cc0
    wne
    #
    @13
    @14
    wb
    #
    @2
    @8
    @2
    @23
    @24
    wa
    @6
    cc0
    wceq
    #
    @7
    cc0
    wceq
    #
    wa
    wn
    #
    @8
    cn
    wcel
    @0
    @23
    @1
    @24
    @28
    @29
    anim12i
    @0
    @64
    @1
    @0
    @62
    @63
    @0
    @6
    cc0
    @0
    @6
    @27
    nnne0d
    neneqd
    intnanrd
    adantr
    @6
    @7
    gcdn0cl
    syl2anc
    nncnd
    @11
    @2
    @4
    @10
    nnne0d
    @58
    c1
    cc
    wcel
    @59
    @60
    wa
    @61
    ax-1cn
    @8
    c1
    @4
    divmul
    mp3an2
    syl12anc
    mpbid
    eqtr3d
end
