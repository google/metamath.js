include "cc0.mm"
include "wceq.mm"
include "wcel.mm"
include "cn0.mm"
include "cz.mm"
include "w3a.mm"
include "creps.mm"
include "co.mm"
include "ccsh.mm"
include "wi.mm"
include "c0.mm"
include "0csh0.mm"
include "repsw0.mm"
include "oveq1d.mm"
include "3eqtr4a.mm"
include "3ad2ant1.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "wn.mm"
include "cn.mm"
include "idd.mm"
include "wne.mm"
include "df-ne.mm"
include "elnnne0.mm"
include "simplbi2com.mm"
include "sylbir.mm"
include "3anim123d.mm"
include "chash.mm"
include "cfv.mm"
include "cmo.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "cword.mm"
include "wa.mm"
include "nnnn0.mm"
include "anim2i.mm"
include "repsw.mm"
include "syl.mm"
include "cshword.mm"
include "stoic3.mm"
include "repswlen.mm"
include "oveq2d.mm"
include "opeq12d.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "3adant3.mm"
include "cmin.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "zmodcl.mm"
include "ancoms.mm"
include "adantr.mm"
include "jca.mm"
include "3adant1.mm"
include "nnre.mm"
include "leidd.mm"
include "3ad2ant2.mm"
include "repswswrd.mm"
include "syl3anc.mm"
include "0nn0.mm"
include "jctil.mm"
include "cr.mm"
include "crp.mm"
include "zre.mm"
include "nnrp.mm"
include "modcl.mm"
include "syl2anr.mm"
include "clt.mm"
include "modlt.mm"
include "ltled.mm"
include "simp1.mm"
include "nn0red.mm"
include "wb.mm"
include "nn0sub.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "nn0ge0d.mm"
include "repswccat.mm"
include "cc.mm"
include "nncn.mm"
include "adantl.mm"
include "nn0cnd.mm"
include "0cnd.mm"
include "npncand.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "syl6.mm"
include "pm2.61i.mm"

theorem repswcshw
  let cS: class S
  let cI: class I
  let cN: class N
  let cV: class V


  assert |- ( ( S e. V /\ N e. NN0 /\ I e. ZZ ) -> ( ( S repeatS N ) cyclShift I ) = ( S repeatS N ) )

  proof
    cN
    cc0
    wceq
    #
    cS
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    cI
    cz
    wcel
    #
    w3a
    #
    cS
    cN
    creps
    co
    #
    cI
    ccsh
    co
    #
    @5
    wceq
    #
    wi
    @4
    @7
    @0
    cS
    cc0
    creps
    co
    #
    cI
    ccsh
    co
    #
    @8
    wceq
    #
    @1
    @2
    @10
    @3
    @1
    c0
    cI
    ccsh
    co
    c0
    @9
    @8
    cI
    0csh0
    @1
    @8
    c0
    cI
    ccsh
    cS
    cV
    repsw0
    #
    oveq1d
    @11
    3eqtr4a
    3ad2ant1
    @0
    @6
    @9
    @5
    @8
    @0
    @5
    @8
    cI
    ccsh
    cN
    cc0
    cS
    creps
    oveq2
    #
    oveq1d
    @12
    eqeq12d
    syl5ibr
    @0
    wn
    #
    @4
    @1
    cN
    cn
    wcel
    #
    @3
    w3a
    #
    @7
    @13
    @1
    @1
    @2
    @14
    @3
    @3
    @13
    @1
    idd
    @13
    cN
    cc0
    wne
    #
    @2
    @14
    wi
    cN
    cc0
    df-ne
    @14
    @2
    @16
    cN
    elnnne0
    simplbi2com
    sylbir
    @13
    @3
    idd
    3anim123d
    @15
    @6
    @5
    cI
    @5
    chash
    cfv
    #
    cmo
    co
    #
    @17
    cop
    #
    csubstr
    co
    #
    @5
    cc0
    @18
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    @5
    cI
    cN
    cmo
    co
    #
    cN
    cop
    #
    csubstr
    co
    #
    @5
    cc0
    @24
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    @5
    @1
    @14
    @5
    cV
    cword
    wcel
    #
    @3
    @6
    @23
    wceq
    @1
    @14
    wa
    #
    @1
    @2
    wa
    #
    @30
    @14
    @2
    @1
    cN
    nnnn0
    #
    anim2i
    #
    cS
    cN
    cV
    repsw
    syl
    cI
    cV
    @5
    cshword
    stoic3
    @1
    @14
    @23
    @29
    wceq
    @3
    @31
    @20
    @26
    @22
    @28
    cconcat
    @31
    @19
    @25
    @5
    csubstr
    @31
    @18
    @24
    @17
    cN
    @31
    @17
    cN
    cI
    cmo
    @31
    @32
    @17
    cN
    wceq
    @34
    cS
    cN
    cV
    repswlen
    syl
    #
    oveq2d
    #
    @35
    opeq12d
    oveq2d
    @31
    @21
    @27
    @5
    csubstr
    @31
    @18
    @24
    cc0
    @36
    opeq2d
    oveq2d
    oveq12d
    3adant3
    @15
    @29
    cS
    cN
    @24
    cmin
    co
    #
    creps
    co
    #
    cS
    @24
    cc0
    cmin
    co
    #
    creps
    co
    #
    cconcat
    co
    #
    cS
    @37
    @39
    caddc
    co
    #
    creps
    co
    #
    @5
    @15
    @26
    @38
    @28
    @40
    cconcat
    @15
    @32
    @24
    cn0
    wcel
    #
    @2
    wa
    #
    cN
    cN
    cle
    wbr
    #
    @26
    @38
    wceq
    @1
    @14
    @32
    @3
    @34
    3adant3
    #
    @14
    @3
    @45
    @1
    @14
    @3
    wa
    #
    @44
    @2
    @3
    @14
    @44
    cI
    cN
    zmodcl
    #
    ancoms
    #
    @14
    @2
    @3
    @33
    adantr
    jca
    3adant1
    @14
    @1
    @46
    @3
    @14
    cN
    cN
    nnre
    #
    leidd
    3ad2ant2
    cS
    cN
    @24
    cN
    cV
    repswswrd
    syl3anc
    @15
    @32
    cc0
    cn0
    wcel
    #
    @44
    wa
    #
    @24
    cN
    cle
    wbr
    #
    @28
    @40
    wceq
    @47
    @14
    @3
    @53
    @1
    @48
    @44
    @52
    @50
    0nn0
    jctil
    3adant1
    @14
    @3
    @54
    @1
    @48
    @24
    cN
    @3
    cI
    cr
    wcel
    #
    cN
    crp
    wcel
    #
    @24
    cr
    wcel
    #
    @14
    cI
    zre
    #
    cN
    nnrp
    #
    cI
    cN
    modcl
    syl2anr
    @14
    cN
    cr
    wcel
    @3
    @51
    adantr
    #
    @3
    @55
    @56
    @24
    cN
    clt
    wbr
    @14
    @58
    @59
    cI
    cN
    modlt
    syl2anr
    #
    ltled
    3adant1
    cS
    cN
    cc0
    @24
    cV
    repswswrd
    syl3anc
    oveq12d
    @15
    @1
    @37
    cn0
    wcel
    #
    @39
    cn0
    wcel
    #
    @41
    @43
    wceq
    @1
    @14
    @3
    simp1
    @15
    @54
    @62
    @14
    @3
    @54
    @1
    @48
    @24
    cN
    @3
    @14
    @57
    @3
    @14
    wa
    #
    @24
    @49
    nn0red
    ancoms
    @60
    @61
    ltled
    3adant1
    @15
    @44
    @2
    @54
    @62
    wb
    @14
    @3
    @44
    @1
    @50
    3adant1
    #
    @14
    @1
    @2
    @3
    @33
    3ad2ant2
    @24
    cN
    nn0sub
    syl2anc
    mpbid
    @15
    cc0
    @24
    cle
    wbr
    #
    @63
    @14
    @3
    @66
    @1
    @3
    @14
    @66
    @64
    @24
    @49
    nn0ge0d
    ancoms
    3adant1
    @15
    @53
    @66
    @63
    wb
    @15
    @44
    @52
    @65
    0nn0
    jctil
    cc0
    @24
    nn0sub
    syl
    mpbid
    cS
    @39
    @37
    cV
    repswccat
    syl3anc
    @15
    @42
    cN
    cS
    creps
    @14
    @3
    @42
    cN
    wceq
    #
    @1
    @3
    @14
    @67
    @64
    @42
    cN
    cc0
    cmin
    co
    #
    cN
    @64
    cN
    @24
    cc0
    @14
    cN
    cc
    wcel
    @3
    cN
    nncn
    #
    adantl
    @64
    @24
    @49
    nn0cnd
    @64
    0cnd
    npncand
    @14
    @68
    cN
    wceq
    @3
    @14
    cN
    @69
    subid1d
    adantl
    eqtrd
    ancoms
    3adant1
    oveq2d
    3eqtrd
    3eqtrd
    syl6
    pm2.61i
end
