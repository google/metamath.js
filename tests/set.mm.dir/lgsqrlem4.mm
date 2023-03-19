include "cfv.mm"
include "ccnv.mm"
include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "c1.mm"
include "cdiv.mm"
include "cfz.mm"
include "c0g.mm"
include "csn.mm"
include "cima.mm"
include "wf1o.mm"
include "wf.mm"
include "wf1.mm"
include "lgsqrlem2.mm"
include "cen.mm"
include "cfn.mm"
include "wb.mm"
include "cdom.mm"
include "fvex.mm"
include "cnvex.mm"
include "imaex.mm"
include "f1dom.mm"
include "syl.mm"
include "chash.mm"
include "cle.mm"
include "eqid.mm"
include "cfield.mm"
include "cidom.mm"
include "cprime.mm"
include "eldifad.mm"
include "znfld.mm"
include "fldidom.mm"
include "cgrp.mm"
include "crg.mm"
include "ccrg.mm"
include "cdomn.mm"
include "isidom.mm"
include "simplbi.mm"
include "crngring.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "cmgp.mm"
include "cmnd.mm"
include "cn0.mm"
include "ringmgp.mm"
include "cdif.mm"
include "cn.mm"
include "oddprm.mm"
include "nnnn0d.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "ringidcl.mm"
include "grpsubcl.mm"
include "syl5eqel.mm"
include "wne.mm"
include "fveq2i.mm"
include "cc0.mm"
include "clt.mm"
include "nngt0d.mm"
include "cur.mm"
include "cascl.mm"
include "wceq.mm"
include "ply1scl1.mm"
include "fveq2d.mm"
include "cbs.mm"
include "cnzr.mm"
include "domnnzr.mm"
include "simplbiim.mm"
include "nzrnz.mm"
include "deg1scl.mm"
include "eqtr3d.mm"
include "deg1pw.mm"
include "syl2anc.mm"
include "3brtr4d.mm"
include "deg1sub.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "deg1nn0clb.mm"
include "mpbird.mm"
include "fta1g.mm"
include "breqtrd.mm"
include "hashfz1.mm"
include "breqtrrd.mm"
include "cvv.mm"
include "hashbnd.mm"
include "mp3an2i.mm"
include "fzfid.mm"
include "hashdom.mm"
include "mpbid.mm"
include "sbth.mm"
include "f1finf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "lgsqrlem3.mm"
include "ffvelrnd.mm"
include "elfzelz.mm"
include "oveq1.mm"
include "cmpt.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fvmpt.mm"
include "f1ocnvfv2.mm"
include "prmnn.mm"
include "zsqcl.mm"
include "zndvds.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "rspcev.mm"

theorem lgsqrlem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let c.1: class .1.
  let c.ex: class .^
  let cG: class G
  let cL: class L
  let c.mi: class .-
  let cO: class O
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume lgsqr.y: |- Y = ( Z/nZ ` P )
  assume lgsqr.s: |- S = ( Poly1 ` Y )
  assume lgsqr.b: |- B = ( Base ` S )
  assume lgsqr.d: |- D = ( deg1 ` Y )
  assume lgsqr.o: |- O = ( eval1 ` Y )
  assume lgsqr.e: |- .^ = ( .g ` ( mulGrp ` S ) )
  assume lgsqr.x: |- X = ( var1 ` Y )
  assume lgsqr.m: |- .- = ( -g ` S )
  assume lgsqr.u: |- .1. = ( 1r ` S )
  assume lgsqr.t: |- T = ( ( ( ( P - 1 ) / 2 ) .^ X ) .- .1. )
  assume lgsqr.l: |- L = ( ZRHom ` Y )
  assume lgsqr.1: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume lgsqr.g: |- G = ( y e. ( 1 ... ( ( P - 1 ) / 2 ) ) |-> ( L ` ( y ^ 2 ) ) )
  assume lgsqr.3: |- ( ph -> A e. ZZ )
  assume lgsqr.4: |- ( ph -> ( A /L P ) = 1 )

  disjoint A x
  disjoint G x
  disjoint O y
  disjoint x y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  disjoint T y
  disjoint L x
  disjoint L y
  disjoint Y x
  disjoint Y y
  disjoint x z
  disjoint G z
  disjoint y z
  disjoint P z
  disjoint ph z
  assert |- ( ph -> E. x e. ZZ P || ( ( x ^ 2 ) - A ) )

  proof
    wph
    cA
    cL
    cfv
    #
    cG
    ccnv
    #
    cfv
    #
    cz
    wcel
    #
    cP
    @2
    c2
    cexp
    co
    #
    cA
    cmin
    co
    #
    cdvds
    wbr
    #
    cP
    vx
    cv
    #
    c2
    cexp
    co
    #
    cA
    cmin
    co
    #
    cdvds
    wbr
    #
    vx
    cz
    wrex
    wph
    @2
    c1
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cfz
    co
    #
    wcel
    #
    @3
    wph
    cT
    cO
    cfv
    #
    ccnv
    #
    cY
    c0g
    cfv
    #
    csn
    #
    cima
    #
    @12
    @0
    @1
    wph
    @12
    @18
    cG
    wf1o
    #
    @18
    @12
    @1
    wf1o
    @18
    @12
    @1
    wf
    wph
    @12
    @18
    cG
    wf1
    #
    @19
    wph
    vy
    cB
    cD
    cP
    cS
    cT
    c.1
    c.ex
    cG
    cL
    c.mi
    cO
    cX
    cY
    lgsqr.y
    lgsqr.s
    lgsqr.b
    lgsqr.d
    lgsqr.o
    lgsqr.e
    lgsqr.x
    lgsqr.m
    lgsqr.u
    lgsqr.t
    lgsqr.l
    lgsqr.1
    lgsqr.g
    lgsqrlem2
    #
    wph
    @12
    @18
    cen
    wbr
    #
    @18
    cfn
    wcel
    #
    @20
    @19
    wb
    wph
    @12
    @18
    cdom
    wbr
    #
    @18
    @12
    cdom
    wbr
    #
    @22
    wph
    @20
    @24
    @21
    @12
    @18
    cG
    @15
    @17
    @14
    cT
    cO
    fvex
    cnvex
    imaex
    #
    f1dom
    syl
    wph
    @18
    chash
    cfv
    #
    @12
    chash
    cfv
    #
    cle
    wbr
    #
    @25
    wph
    @27
    @11
    @28
    cle
    wph
    @27
    cT
    cD
    cfv
    #
    @11
    cle
    wph
    cB
    cD
    cS
    cY
    cT
    cO
    @16
    cS
    c0g
    cfv
    #
    lgsqr.s
    lgsqr.b
    lgsqr.d
    lgsqr.o
    @16
    eqid
    #
    @31
    eqid
    #
    wph
    cY
    cfield
    wcel
    #
    cY
    cidom
    wcel
    #
    wph
    cP
    cprime
    wcel
    #
    @34
    wph
    cP
    cprime
    c2
    csn
    #
    lgsqr.1
    eldifad
    #
    cP
    cY
    lgsqr.y
    znfld
    syl
    cY
    fldidom
    syl
    #
    wph
    cT
    @11
    cX
    c.ex
    co
    #
    c.1
    c.mi
    co
    #
    cB
    lgsqr.t
    wph
    cS
    cgrp
    wcel
    #
    @40
    cB
    wcel
    #
    c.1
    cB
    wcel
    #
    @41
    cB
    wcel
    wph
    cS
    crg
    wcel
    #
    @42
    wph
    cY
    crg
    wcel
    #
    @45
    wph
    cY
    ccrg
    wcel
    #
    @46
    wph
    @35
    @47
    @39
    @35
    @47
    cY
    cdomn
    wcel
    #
    cY
    isidom
    #
    simplbi
    syl
    cY
    crngring
    syl
    #
    cS
    cY
    lgsqr.s
    ply1ring
    syl
    #
    cS
    ringgrp
    syl
    wph
    cS
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    @11
    cn0
    wcel
    #
    cX
    cB
    wcel
    #
    @43
    wph
    @45
    @53
    @51
    cS
    @52
    @52
    eqid
    #
    ringmgp
    syl
    wph
    @11
    wph
    cP
    cprime
    @37
    cdif
    wcel
    @11
    cn
    wcel
    lgsqr.1
    cP
    oddprm
    syl
    #
    nnnn0d
    #
    wph
    @46
    @55
    @50
    cB
    cS
    cY
    cX
    lgsqr.x
    lgsqr.s
    lgsqr.b
    vr1cl
    syl
    cB
    c.ex
    @52
    @11
    cX
    cB
    cS
    @52
    @56
    lgsqr.b
    mgpbas
    lgsqr.e
    mulgnn0cl
    syl3anc
    #
    wph
    @45
    @44
    @51
    cB
    cS
    c.1
    lgsqr.b
    lgsqr.u
    ringidcl
    syl
    #
    cB
    cS
    c.mi
    @40
    c.1
    lgsqr.b
    lgsqr.m
    grpsubcl
    syl3anc
    syl5eqel
    #
    wph
    cT
    @31
    wne
    #
    @30
    cn0
    wcel
    #
    wph
    @30
    @11
    cn0
    wph
    @30
    @40
    cD
    cfv
    #
    @11
    wph
    @30
    @41
    cD
    cfv
    @64
    cT
    @41
    cD
    lgsqr.t
    fveq2i
    wph
    cB
    cD
    cY
    @40
    c.1
    c.mi
    cS
    lgsqr.s
    lgsqr.d
    @50
    lgsqr.b
    lgsqr.m
    @59
    @60
    wph
    cc0
    @11
    c.1
    cD
    cfv
    #
    @64
    clt
    wph
    @11
    @57
    nngt0d
    wph
    cY
    cur
    cfv
    #
    cS
    cascl
    cfv
    #
    cfv
    #
    cD
    cfv
    #
    @65
    cc0
    wph
    @68
    c.1
    cD
    wph
    @46
    @68
    c.1
    wceq
    @50
    @67
    cS
    cY
    @66
    c.1
    lgsqr.s
    @67
    eqid
    #
    @66
    eqid
    #
    lgsqr.u
    ply1scl1
    syl
    fveq2d
    wph
    @46
    @66
    cY
    cbs
    cfv
    #
    wcel
    #
    @66
    @16
    wne
    #
    @69
    cc0
    wceq
    @50
    wph
    @46
    @73
    @50
    @72
    cY
    @66
    @72
    eqid
    #
    @71
    ringidcl
    syl
    wph
    cY
    cnzr
    wcel
    #
    @74
    wph
    @35
    @76
    @39
    @35
    @47
    @48
    @76
    @49
    cY
    domnnzr
    simplbiim
    syl
    #
    cY
    @66
    @16
    @71
    @32
    nzrnz
    syl
    @67
    cD
    cS
    cY
    @66
    @72
    @16
    lgsqr.d
    lgsqr.s
    @75
    @70
    @32
    deg1scl
    syl3anc
    eqtr3d
    wph
    @76
    @54
    @64
    @11
    wceq
    @77
    @58
    cD
    cS
    cY
    c.ex
    @11
    @52
    cX
    lgsqr.d
    lgsqr.s
    lgsqr.x
    @56
    lgsqr.e
    deg1pw
    syl2anc
    #
    3brtr4d
    deg1sub
    syl5eq
    @78
    eqtrd
    #
    @58
    eqeltrd
    wph
    @46
    cT
    cB
    wcel
    @62
    @63
    wb
    @50
    @61
    cB
    cD
    cS
    cY
    cT
    @31
    lgsqr.d
    lgsqr.s
    @33
    lgsqr.b
    deg1nn0clb
    syl2anc
    mpbird
    fta1g
    @79
    breqtrd
    #
    wph
    @54
    @28
    @11
    wceq
    @58
    @11
    hashfz1
    syl
    breqtrrd
    wph
    @23
    @12
    cfn
    wcel
    @29
    @25
    wb
    @18
    cvv
    wcel
    wph
    @54
    @27
    @11
    cle
    wbr
    @23
    @26
    @58
    @80
    @18
    @11
    cvv
    hashbnd
    mp3an2i
    #
    wph
    c1
    @11
    fzfid
    @18
    @12
    cfn
    hashdom
    syl2anc
    mpbid
    @12
    @18
    sbth
    syl2anc
    @81
    @12
    @18
    cG
    f1finf1o
    syl2anc
    mpbid
    #
    @12
    @18
    cG
    f1ocnv
    @18
    @12
    @1
    f1of
    3syl
    wph
    vy
    cA
    cB
    cD
    cP
    cS
    cT
    c.1
    c.ex
    cG
    cL
    c.mi
    cO
    cX
    cY
    lgsqr.y
    lgsqr.s
    lgsqr.b
    lgsqr.d
    lgsqr.o
    lgsqr.e
    lgsqr.x
    lgsqr.m
    lgsqr.u
    lgsqr.t
    lgsqr.l
    lgsqr.1
    lgsqr.g
    lgsqr.3
    lgsqr.4
    lgsqrlem3
    #
    ffvelrnd
    #
    @2
    c1
    @11
    elfzelz
    syl
    #
    wph
    @4
    cL
    cfv
    #
    @0
    wceq
    #
    @6
    wph
    @2
    cG
    cfv
    #
    @86
    @0
    wph
    @13
    @88
    @86
    wceq
    @84
    vx
    @2
    @8
    cL
    cfv
    #
    @86
    @12
    cG
    @7
    @2
    wceq
    #
    @8
    @4
    cL
    @7
    @2
    c2
    cexp
    oveq1
    #
    fveq2d
    cG
    vy
    @12
    vy
    cv
    #
    c2
    cexp
    co
    #
    cL
    cfv
    #
    cmpt
    vx
    @12
    @89
    cmpt
    lgsqr.g
    vy
    vx
    @12
    @94
    @89
    @92
    @7
    wceq
    @93
    @8
    cL
    @92
    @7
    c2
    cexp
    oveq1
    fveq2d
    cbvmptv
    eqtri
    @4
    cL
    fvex
    fvmpt
    syl
    wph
    @19
    @0
    @18
    wcel
    @88
    @0
    wceq
    @82
    @83
    @12
    @18
    @0
    cG
    f1ocnvfv2
    syl2anc
    eqtr3d
    wph
    cP
    cn0
    wcel
    @4
    cz
    wcel
    #
    cA
    cz
    wcel
    @87
    @6
    wb
    wph
    cP
    wph
    @36
    cP
    cn
    wcel
    @38
    cP
    prmnn
    syl
    nnnn0d
    wph
    @3
    @95
    @85
    @2
    zsqcl
    syl
    lgsqr.3
    @4
    cA
    cL
    cP
    cY
    lgsqr.y
    lgsqr.l
    zndvds
    syl3anc
    mpbid
    @10
    @6
    vx
    @2
    cz
    @90
    @9
    @5
    cP
    cdvds
    @90
    @8
    @4
    cA
    cmin
    @91
    oveq1d
    breq2d
    rspcev
    syl2anc
end
