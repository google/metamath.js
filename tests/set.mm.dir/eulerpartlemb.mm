include "cn.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "csn.mm"
include "cif.mm"
include "cixp.mm"
include "cfn.mm"
include "wss.mm"
include "wtru.mm"
include "fzfid.mm"
include "wa.mm"
include "fzfi.mm"
include "snfi.mm"
include "keepel.mm"
include "a1i.mm"
include "cdif.mm"
include "wn.mm"
include "wceq.mm"
include "eldifn.mm"
include "adantl.mm"
include "iffalse.mm"
include "eqimss.mm"
include "3syl.mm"
include "ixpfi2.mm"
include "trud.mm"
include "cn0.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "cfv.mm"
include "cmul.mm"
include "csu.mm"
include "w3a.mm"
include "eulerpartleme.mm"
include "wfn.mm"
include "wral.mm"
include "ffn.mm"
include "3ad2ant1.mm"
include "cle.mm"
include "wbr.mm"
include "ffvelrn.mm"
include "3ad2antl1.mm"
include "nn0red.mm"
include "cr.mm"
include "nnre.mm"
include "remulcld.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "adantr.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "nnnn0d.mm"
include "nn0mulcld.mm"
include "nn0cnd.mm"
include "cvv.mm"
include "simpl.mm"
include "csupp.mm"
include "nnex.mm"
include "frnnn0supp.mm"
include "mpan.mm"
include "syl.mm"
include "0nn0.mm"
include "suppssr.mm"
include "oveq1d.mm"
include "cc.mm"
include "eldifi.mm"
include "nncn.mm"
include "mul02.mm"
include "eqtrd.mm"
include "cuz.mm"
include "nnuz.mm"
include "eqimssi.mm"
include "sumss.mm"
include "simpr.mm"
include "fsumnn0cl.mm"
include "eqeltrrd.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "3impia.mm"
include "nn0ge0d.mm"
include "nnge1.mm"
include "lemulge11d.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "simprr.mm"
include "fsumge1.mm"
include "expr.mm"
include "eldif.mm"
include "ralrimiva.mm"
include "eqeq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "sylan2br.mm"
include "fsumge0.mm"
include "adantrr.mm"
include "eqbrtrd.mm"
include "pm2.61d.mm"
include "breqtrd.mm"
include "3adantl3.mm"
include "simpl3.mm"
include "letrd.mm"
include "cz.mm"
include "wb.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nn0zd.mm"
include "elfz5.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "iftrue.mm"
include "eleqtrrd.mm"
include "wi.mm"
include "nnnn0.mm"
include "lemulge12.mm"
include "syl21anc.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "syld.mm"
include "syl5.mm"
include "sylibrd.mm"
include "con3d.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "imp.mm"
include "fvex.mm"
include "elsn.mm"
include "sylibr.mm"
include "pm2.61dan.mm"
include "vex.mm"
include "elixp.mm"
include "sylanbrc.mm"
include "sylbi.mm"
include "ssriv.mm"
include "ssfi.mm"
include "mp2an.mm"

theorem eulerpartlemb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cP: class P
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vr: setvar r
  assume eulerpart.p: |- P = { f e. ( NN0 ^m NN ) | ( ( `' f " NN ) e. Fin /\ sum_ k e. NN ( ( f ` k ) x. k ) = N ) }
  assume eulerpart.o: |- O = { g e. P | A. n e. ( `' g " NN ) -. 2 || n }
  assume eulerpart.d: |- D = { g e. P | A. n e. NN ( g ` n ) <_ 1 }
  assume eulerpart.j: |- J = { z e. NN | -. 2 || z }
  assume eulerpart.f: |- F = ( x e. J , y e. NN0 |-> ( ( 2 ^ y ) x. x ) )
  assume eulerpart.h: |- H = { r e. ( ( ~P NN0 i^i Fin ) ^m J ) | ( r supp (/) ) e. Fin }
  assume eulerpart.m: |- M = ( r e. H |-> { <. x , y >. | ( x e. J /\ y e. ( r ` x ) ) } )

  disjoint f g
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint N f
  disjoint N g
  disjoint N x
  disjoint P g
  assert |- P e. Fin

  proof
    vx
    cn
    vx
    cv
    #
    c1
    cN
    cfz
    co
    #
    wcel
    #
    cc0
    cN
    cfz
    co
    #
    cc0
    csn
    #
    cif
    #
    cixp
    #
    cfn
    wcel
    #
    cP
    @6
    wss
    cP
    cfn
    wcel
    @7
    wtru
    vx
    cn
    @5
    @1
    cc0
    wtru
    c1
    cN
    fzfid
    @5
    cfn
    wcel
    wtru
    @0
    cn
    wcel
    #
    wa
    @2
    @3
    @4
    cfn
    cc0
    cN
    fzfi
    cc0
    snfi
    keepel
    a1i
    wtru
    @0
    cn
    @1
    cdif
    wcel
    #
    wa
    @2
    wn
    #
    @5
    @4
    wceq
    #
    @5
    @4
    wss
    @9
    @10
    wtru
    @0
    cn
    @1
    eldifn
    adantl
    @2
    @3
    @4
    iffalse
    #
    @5
    @4
    eqimss
    3syl
    ixpfi2
    trud
    vg
    cP
    @6
    vg
    cv
    #
    cP
    wcel
    cn
    cn0
    @13
    wf
    #
    @13
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    cn
    vk
    cv
    #
    @13
    cfv
    #
    @17
    cmul
    co
    #
    vk
    csu
    #
    cN
    wceq
    #
    w3a
    #
    @13
    @6
    wcel
    #
    @13
    cP
    vf
    vk
    cN
    eulerpart.p
    eulerpartleme
    @22
    @13
    cn
    wfn
    #
    @0
    @13
    cfv
    #
    @5
    wcel
    #
    vx
    cn
    wral
    @23
    @14
    @16
    @24
    @21
    cn
    cn0
    @13
    ffn
    3ad2ant1
    @22
    @26
    vx
    cn
    @22
    @8
    wa
    #
    @2
    @26
    @27
    @2
    wa
    @25
    @3
    @5
    @27
    @25
    @3
    wcel
    #
    @2
    @27
    @28
    @25
    cN
    cle
    wbr
    #
    @27
    @25
    @25
    @0
    cmul
    co
    #
    cN
    @27
    @25
    @14
    @16
    @8
    @25
    cn0
    wcel
    #
    @21
    cn
    cn0
    @0
    @13
    ffvelrn
    3ad2antl1
    #
    nn0red
    #
    @27
    @25
    @0
    @33
    @8
    @0
    cr
    wcel
    #
    @22
    @0
    nnre
    adantl
    #
    remulcld
    #
    @27
    cN
    @22
    cN
    cn0
    wcel
    #
    @8
    @14
    @16
    @21
    @37
    @14
    @16
    wa
    #
    @20
    cn0
    wcel
    @21
    @37
    @38
    @15
    @19
    vk
    csu
    #
    @20
    cn0
    @38
    @15
    cn
    @19
    vk
    c1
    @38
    @13
    cdm
    #
    @15
    cn
    @13
    cn
    cnvimass
    @14
    @40
    cn
    wceq
    @16
    cn
    cn0
    @13
    fdm
    adantr
    syl5sseq
    #
    @38
    @17
    @15
    wcel
    #
    wa
    #
    @19
    @43
    @18
    @17
    @38
    @42
    @17
    cn
    wcel
    #
    @18
    cn0
    wcel
    #
    @38
    @15
    cn
    @17
    @41
    sselda
    #
    @14
    @44
    @45
    @16
    cn
    cn0
    @17
    @13
    ffvelrn
    adantlr
    syldan
    @43
    @17
    @46
    nnnn0d
    nn0mulcld
    #
    nn0cnd
    @38
    @17
    cn
    @15
    cdif
    #
    wcel
    #
    wa
    #
    @19
    cc0
    @17
    cmul
    co
    #
    cc0
    @50
    @18
    cc0
    @17
    cmul
    @38
    cn
    cn0
    cn0
    @13
    cvv
    @15
    @17
    cc0
    @14
    @16
    simpl
    @38
    @13
    cc0
    csupp
    co
    #
    @15
    wceq
    #
    @52
    @15
    wss
    @14
    @53
    @16
    cn
    cvv
    wcel
    #
    @14
    @53
    nnex
    @13
    cn
    cvv
    frnnn0supp
    mpan
    adantr
    @52
    @15
    eqimss
    syl
    @54
    @38
    nnex
    a1i
    cc0
    cn0
    wcel
    @38
    0nn0
    a1i
    suppssr
    oveq1d
    @50
    @44
    @17
    cc
    wcel
    @51
    cc0
    wceq
    @49
    @44
    @38
    @17
    cn
    @15
    eldifi
    adantl
    @17
    nncn
    @17
    mul02
    3syl
    eqtrd
    #
    cn
    c1
    cuz
    cfv
    #
    wss
    @38
    cn
    @56
    nnuz
    eqimssi
    a1i
    sumss
    #
    @38
    @15
    @19
    vk
    @14
    @16
    simpr
    #
    @47
    fsumnn0cl
    eqeltrrd
    @20
    cN
    cn0
    eleq1
    syl5ibcom
    3impia
    adantr
    #
    nn0red
    #
    @27
    @25
    @0
    @33
    @35
    @27
    @25
    @32
    nn0ge0d
    @8
    c1
    @0
    cle
    wbr
    @22
    @0
    nnge1
    adantl
    lemulge11d
    @27
    @30
    @20
    cN
    cle
    @14
    @16
    @8
    @30
    @20
    cle
    wbr
    @21
    @38
    @8
    wa
    #
    @30
    @39
    @20
    cle
    @61
    @0
    @15
    wcel
    #
    @30
    @39
    cle
    wbr
    #
    @38
    @8
    @62
    @63
    @38
    @8
    @62
    wa
    #
    wa
    @15
    @19
    @30
    vk
    @0
    @38
    @16
    @64
    @58
    adantr
    @38
    @42
    @19
    cr
    wcel
    @64
    @43
    @19
    @47
    nn0red
    adantlr
    @38
    @42
    cc0
    @19
    cle
    wbr
    @64
    @43
    @19
    @47
    nn0ge0d
    adantlr
    @17
    @0
    wceq
    #
    @18
    @25
    @17
    @0
    cmul
    @17
    @0
    @13
    fveq2
    @65
    id
    oveq12d
    #
    @38
    @8
    @62
    simprr
    fsumge1
    expr
    @38
    @8
    @62
    wn
    #
    @63
    @38
    @8
    @67
    wa
    #
    wa
    @30
    cc0
    @39
    cle
    @68
    @38
    @0
    @48
    wcel
    #
    @30
    cc0
    wceq
    #
    @0
    cn
    @15
    eldif
    @38
    @19
    cc0
    wceq
    #
    vk
    @48
    wral
    @69
    @70
    @38
    @71
    vk
    @48
    @55
    ralrimiva
    @71
    @70
    vk
    @0
    @48
    @65
    @19
    @30
    cc0
    @66
    eqeq1d
    rspccva
    sylan
    sylan2br
    @38
    @8
    cc0
    @39
    cle
    wbr
    @67
    @61
    @15
    @19
    vk
    @38
    @16
    @8
    @58
    adantr
    @61
    @42
    wa
    #
    @19
    @38
    @42
    @19
    cn0
    wcel
    @8
    @47
    adantlr
    #
    nn0red
    @72
    @19
    @73
    nn0ge0d
    fsumge0
    adantrr
    eqbrtrd
    expr
    pm2.61d
    @38
    @39
    @20
    wceq
    @8
    @57
    adantr
    breqtrd
    3adantl3
    @14
    @16
    @21
    @8
    simpl3
    breqtrd
    #
    letrd
    @27
    @25
    cc0
    cuz
    cfv
    #
    wcel
    cN
    cz
    wcel
    #
    @28
    @29
    wb
    @27
    @25
    cn0
    @75
    @32
    nn0uz
    syl6eleq
    @27
    cN
    @59
    nn0zd
    #
    @25
    cc0
    cN
    elfz5
    syl2anc
    mpbird
    adantr
    @2
    @5
    @3
    wceq
    @27
    @2
    @3
    @4
    iftrue
    adantl
    eleqtrrd
    @27
    @10
    wa
    #
    @25
    @4
    @5
    @78
    @25
    cc0
    wceq
    #
    @25
    @4
    wcel
    @27
    @10
    @79
    @27
    @10
    @25
    cn
    wcel
    #
    wn
    @79
    @27
    @80
    @2
    @27
    @80
    @0
    cN
    cle
    wbr
    #
    @2
    @80
    c1
    @25
    cle
    wbr
    #
    @27
    @81
    @25
    nnge1
    @27
    @82
    @0
    @30
    cle
    wbr
    #
    @81
    @27
    @34
    @25
    cr
    wcel
    #
    cc0
    @0
    cle
    wbr
    #
    @82
    @83
    wi
    @35
    @33
    @27
    @0
    @8
    @0
    cn0
    wcel
    @22
    @0
    nnnn0
    adantl
    nn0ge0d
    @34
    @84
    wa
    @85
    @82
    @83
    @0
    @25
    lemulge12
    expr
    syl21anc
    @27
    @83
    @30
    cN
    cle
    wbr
    #
    @81
    @74
    @27
    @34
    @30
    cr
    wcel
    cN
    cr
    wcel
    @83
    @86
    wa
    @81
    wi
    @35
    @36
    @60
    @0
    @30
    cN
    letr
    syl3anc
    mpan2d
    syld
    syl5
    @27
    @0
    @56
    wcel
    @76
    @2
    @81
    wb
    @27
    @0
    cn
    @56
    @22
    @8
    simpr
    nnuz
    syl6eleq
    @77
    @0
    c1
    cN
    elfz5
    syl2anc
    sylibrd
    con3d
    @27
    @80
    @79
    @27
    @31
    @80
    @79
    wo
    @32
    @25
    elnn0
    sylib
    ord
    syld
    imp
    @25
    cc0
    @0
    @13
    fvex
    elsn
    sylibr
    @10
    @11
    @27
    @12
    adantl
    eleqtrrd
    pm2.61dan
    ralrimiva
    vx
    cn
    @5
    @13
    vg
    vex
    elixp
    sylanbrc
    sylbi
    ssriv
    @6
    cP
    ssfi
    mp2an
end
