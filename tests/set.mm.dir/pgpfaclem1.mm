include "cword.mm"
include "wcel.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "csn.mm"
include "cfv.mm"
include "csubg.mm"
include "cress.mm"
include "ccyg.mm"
include "cpgp.mm"
include "crn.mm"
include "cin.mm"
include "wss.mm"
include "cbs.mm"
include "cmre.mm"
include "cgrp.mm"
include "cacs.mm"
include "subggrp.mm"
include "syl.mm"
include "eqid.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "subgbas.mm"
include "eleqtrd.mm"
include "mrcsncl.mm"
include "syl2anc.mm"
include "wb.mm"
include "subsubg.mm"
include "mpbid.mm"
include "simpld.mm"
include "oveq1i.mm"
include "simprd.mm"
include "ressabs.mm"
include "syl5eq.mm"
include "cycsubgcyg2.mm"
include "eqeltrrd.mm"
include "cprime.mm"
include "pgpprm.mm"
include "subgpgp.mm"
include "brelrng.mm"
include "syl3anc.mm"
include "elind.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "cats1cld.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "c0g.mm"
include "ccntz.mm"
include "wf.mm"
include "wrdf.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "fss.mm"
include "sylancl.mm"
include "c0.mm"
include "c1.mm"
include "caddc.mm"
include "fzodisj.mm"
include "cz.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0zd.mm"
include "fzosn.mm"
include "ineq2d.mm"
include "syl5reqr.mm"
include "cun.mm"
include "cs1.mm"
include "cconcat.mm"
include "fveq2i.mm"
include "s1cld.mm"
include "ccatlen.mm"
include "s1len.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzosplitsn.mm"
include "eqtrd.mm"
include "cres.mm"
include "cop.mm"
include "cats1un.mm"
include "reseq1d.mm"
include "wfn.mm"
include "wn.mm"
include "ffn.mm"
include "fzonel.mm"
include "fsnunres.mm"
include "breqtrrd.mm"
include "cvv.mm"
include "fvex.mm"
include "dprdsn.mm"
include "sylancr.mm"
include "ssun2.mm"
include "snss.mm"
include "mpbir.mm"
include "syl5eleqr.mm"
include "fnressn.mm"
include "fveq1i.mm"
include "nn0cnd.mm"
include "addid2d.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "cn.mm"
include "1nn.mm"
include "a1i.mm"
include "syl5eqel.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "ccatval3.mm"
include "s1fv.mm"
include "mp1i.mm"
include "3eqtrd.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "dprdsubg.mm"
include "ablcntzd.mm"
include "ineq12d.mm"
include "incom.mm"
include "subg0.mm"
include "syl6eqr.mm"
include "3eqtr4d.mm"
include "dmdprdsplit2.mm"
include "clsm.mm"
include "dprdsplit.mm"
include "oveq12d.mm"
include "cabl.mm"
include "lsmcom.mm"
include "subgss.mm"
include "sseqtr4d.mm"
include "subglsm.mm"
include "breq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem pgpfaclem1
  let wph: wff ph
  let vt: setvar t
  let cB: class B
  let cC: class C
  let cP: class P
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  assume pgpfac.b: |- B = ( Base ` G )
  assume pgpfac.c: |- C = { r e. ( SubGrp ` G ) | ( G |`s r ) e. ( CycGrp i^i ran pGrp ) }
  assume pgpfac.g: |- ( ph -> G e. Abel )
  assume pgpfac.p: |- ( ph -> P pGrp G )
  assume pgpfac.f: |- ( ph -> B e. Fin )
  assume pgpfac.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume pgpfac.a: |- ( ph -> A. t e. ( SubGrp ` G ) ( t C. U -> E. s e. Word C ( G dom DProd s /\ ( G DProd s ) = t ) ) )
  assume pgpfac.h: |- H = ( G |`s U )
  assume pgpfac.k: |- K = ( mrCls ` ( SubGrp ` H ) )
  assume pgpfac.o: |- O = ( od ` H )
  assume pgpfac.e: |- E = ( gEx ` H )
  assume pgpfac.0: |- .0. = ( 0g ` H )
  assume pgpfac.l: |- .(+) = ( LSSum ` H )
  assume pgpfac.1: |- ( ph -> E =/= 1 )
  assume pgpfac.x: |- ( ph -> X e. U )
  assume pgpfac.oe: |- ( ph -> ( O ` X ) = E )
  assume pgpfac.w: |- ( ph -> W e. ( SubGrp ` H ) )
  assume pgpfac.i: |- ( ph -> ( ( K ` { X } ) i^i W ) = { .0. } )
  assume pgpfac.s: |- ( ph -> ( ( K ` { X } ) .(+) W ) = U )
  assume pgpfac.2: |- ( ph -> S e. Word C )
  assume pgpfac.4: |- ( ph -> G dom DProd S )
  assume pgpfac.5: |- ( ph -> ( G DProd S ) = W )
  assume pgpfac.t: |- T = ( S ++ <" ( K ` { X } ) "> )

  disjoint s t
  disjoint C s
  disjoint C t
  disjoint r s
  disjoint r t
  disjoint G r
  disjoint G s
  disjoint G t
  disjoint K r
  disjoint K s
  disjoint ph t
  disjoint B s
  disjoint B t
  disjoint U r
  disjoint U s
  disjoint U t
  disjoint W s
  disjoint W t
  disjoint X r
  disjoint X s
  disjoint T s
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a w
  disjoint a x
  disjoint C a
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint u w
  disjoint u x
  disjoint C u
  disjoint w x
  disjoint C w
  disjoint C x
  disjoint a r
  disjoint G a
  disjoint r u
  disjoint r w
  disjoint r x
  disjoint G u
  disjoint G w
  disjoint G x
  disjoint a ph
  disjoint ph u
  disjoint ph w
  disjoint ph x
  disjoint B x
  disjoint P w
  disjoint U a
  disjoint U w
  disjoint U x
  disjoint W a
  assert |- ( ph -> E. s e. Word C ( G dom DProd s /\ ( G DProd s ) = U ) )

  proof
    wph
    cT
    cC
    cword
    #
    wcel
    #
    cG
    cT
    cdprd
    cdm
    #
    wbr
    #
    cG
    cT
    cdprd
    co
    #
    cU
    wceq
    #
    cG
    vs
    cv
    #
    @2
    wbr
    #
    cG
    @6
    cdprd
    co
    #
    cU
    wceq
    #
    wa
    #
    vs
    @0
    wrex
    wph
    cC
    cS
    cT
    cX
    csn
    #
    cK
    cfv
    #
    pgpfac.t
    pgpfac.2
    wph
    @12
    cG
    csubg
    cfv
    #
    wcel
    #
    cG
    @12
    cress
    co
    #
    ccyg
    cpgp
    crn
    #
    cin
    #
    wcel
    #
    @12
    cC
    wcel
    #
    wph
    @14
    @12
    cU
    wss
    #
    wph
    @12
    cH
    csubg
    cfv
    #
    wcel
    #
    @14
    @20
    wa
    #
    wph
    @21
    cH
    cbs
    cfv
    #
    cmre
    cfv
    wcel
    #
    cX
    @24
    wcel
    #
    @22
    wph
    cH
    cgrp
    wcel
    #
    @21
    @24
    cacs
    cfv
    wcel
    @25
    wph
    cU
    @13
    wcel
    #
    @27
    pgpfac.u
    cU
    cG
    cH
    pgpfac.h
    subggrp
    syl
    #
    @24
    cH
    @24
    eqid
    #
    subgacs
    @21
    @24
    acsmre
    3syl
    wph
    cX
    cU
    @24
    pgpfac.x
    wph
    @28
    cU
    @24
    wceq
    pgpfac.u
    cU
    cG
    cH
    pgpfac.h
    subgbas
    syl
    #
    eleqtrd
    #
    @21
    cX
    cK
    @24
    pgpfac.k
    mrcsncl
    syl2anc
    wph
    @28
    @22
    @23
    wb
    pgpfac.u
    @12
    cU
    cG
    cH
    pgpfac.h
    subsubg
    syl
    mpbid
    #
    simpld
    #
    wph
    ccyg
    @16
    @15
    wph
    cH
    @12
    cress
    co
    #
    @15
    ccyg
    wph
    @35
    cG
    cU
    cress
    co
    #
    @12
    cress
    co
    #
    @15
    cH
    @36
    @12
    cress
    pgpfac.h
    oveq1i
    wph
    @28
    @20
    @37
    @15
    wceq
    pgpfac.u
    wph
    @14
    @20
    @33
    simprd
    #
    cU
    @12
    cG
    @13
    ressabs
    syl2anc
    syl5eq
    wph
    @27
    @26
    @35
    ccyg
    wcel
    @29
    @32
    cX
    @24
    cH
    cK
    @30
    pgpfac.k
    cycsubgcyg2
    syl2anc
    eqeltrrd
    #
    wph
    cP
    cprime
    wcel
    #
    @15
    ccyg
    wcel
    cP
    @15
    cpgp
    wbr
    #
    @15
    @16
    wcel
    wph
    cP
    cG
    cpgp
    wbr
    #
    @40
    pgpfac.p
    cP
    cG
    pgpprm
    syl
    @39
    wph
    @42
    @14
    @41
    pgpfac.p
    @34
    cP
    @12
    cG
    subgpgp
    syl2anc
    cP
    @15
    cpgp
    cprime
    ccyg
    brelrng
    syl3anc
    elind
    cG
    vr
    cv
    #
    cress
    co
    #
    @17
    wcel
    #
    @18
    vr
    @12
    @13
    cC
    @43
    @12
    wceq
    @44
    @15
    @17
    @43
    @12
    cG
    cress
    oveq2
    eleq1d
    pgpfac.c
    elrab2
    sylanbrc
    #
    cats1cld
    #
    wph
    cc0
    cS
    chash
    cfv
    #
    cfzo
    co
    #
    @48
    csn
    #
    cT
    cG
    cc0
    cT
    chash
    cfv
    #
    cfzo
    co
    #
    cG
    c0g
    cfv
    #
    cG
    ccntz
    cfv
    #
    wph
    @52
    cC
    cT
    wf
    #
    cC
    @13
    wss
    @52
    @13
    cT
    wf
    wph
    @1
    @55
    @47
    cC
    cT
    wrdf
    #
    syl
    cC
    @45
    vr
    @13
    crab
    @13
    pgpfac.c
    @45
    vr
    @13
    ssrab2
    eqsstri
    @52
    cC
    @13
    cT
    fss
    sylancl
    #
    wph
    c0
    @49
    @48
    @48
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cin
    @49
    @50
    cin
    cc0
    @48
    @58
    fzodisj
    wph
    @59
    @50
    @49
    wph
    @48
    cz
    wcel
    @59
    @50
    wceq
    wph
    @48
    wph
    cS
    @0
    wcel
    #
    @48
    cn0
    wcel
    pgpfac.2
    cC
    cS
    lencl
    syl
    #
    nn0zd
    @48
    fzosn
    syl
    ineq2d
    syl5reqr
    #
    wph
    @52
    cc0
    @58
    cfzo
    co
    #
    @49
    @50
    cun
    #
    wph
    @51
    @58
    cc0
    cfzo
    wph
    @51
    @48
    @12
    cs1
    #
    chash
    cfv
    #
    caddc
    co
    #
    @58
    wph
    @51
    cS
    @65
    cconcat
    co
    #
    chash
    cfv
    #
    @67
    cT
    @68
    chash
    pgpfac.t
    fveq2i
    wph
    @60
    @65
    @0
    wcel
    #
    @69
    @67
    wceq
    pgpfac.2
    wph
    @12
    cC
    @46
    s1cld
    #
    cC
    cS
    @65
    ccatlen
    syl2anc
    syl5eq
    @66
    c1
    @48
    caddc
    @12
    s1len
    #
    oveq2i
    syl6eq
    oveq2d
    wph
    @48
    cc0
    cuz
    cfv
    #
    wcel
    @63
    @64
    wceq
    wph
    @48
    cn0
    @73
    @61
    nn0uz
    syl6eleq
    cc0
    @48
    fzosplitsn
    syl
    eqtrd
    #
    @54
    eqid
    #
    @53
    eqid
    #
    wph
    cG
    cS
    cT
    @49
    cres
    #
    @2
    pgpfac.4
    wph
    @77
    cS
    @48
    @12
    cop
    #
    csn
    #
    cun
    #
    @49
    cres
    #
    cS
    wph
    cT
    @80
    @49
    wph
    cT
    @68
    @80
    pgpfac.t
    wph
    @60
    @19
    @68
    @80
    wceq
    pgpfac.2
    @46
    cS
    @12
    cC
    cats1un
    syl2anc
    syl5eq
    reseq1d
    wph
    cS
    @49
    wfn
    #
    @48
    @49
    wcel
    wn
    @81
    cS
    wceq
    wph
    @60
    @49
    cC
    cS
    wf
    @82
    pgpfac.2
    cC
    cS
    wrdf
    @49
    cC
    cS
    ffn
    3syl
    cc0
    @48
    fzonel
    @49
    cS
    @48
    @12
    fsnunres
    sylancl
    eqtrd
    #
    breqtrrd
    #
    wph
    cG
    @79
    cT
    @50
    cres
    #
    @2
    wph
    cG
    @79
    @2
    wbr
    #
    cG
    @79
    cdprd
    co
    #
    @12
    wceq
    #
    wph
    @48
    cvv
    wcel
    @14
    @86
    @88
    wa
    cS
    chash
    fvex
    #
    @34
    @48
    @12
    cG
    cvv
    dprdsn
    sylancr
    #
    simpld
    wph
    @85
    @48
    @48
    cT
    cfv
    #
    cop
    #
    csn
    #
    @79
    wph
    cT
    @52
    wfn
    #
    @48
    @52
    wcel
    @85
    @93
    wceq
    wph
    @1
    @55
    @94
    @47
    @56
    @52
    cC
    cT
    ffn
    3syl
    wph
    @48
    @64
    @52
    @48
    @64
    wcel
    @50
    @64
    wss
    @50
    @49
    ssun2
    @48
    @64
    @89
    snss
    mpbir
    @74
    syl5eleqr
    @52
    @48
    cT
    fnressn
    syl2anc
    wph
    @92
    @78
    wph
    @91
    @12
    @48
    wph
    @91
    cc0
    @48
    caddc
    co
    #
    @68
    cfv
    #
    cc0
    @65
    cfv
    #
    @12
    wph
    @91
    @48
    @68
    cfv
    @96
    @48
    cT
    @68
    pgpfac.t
    fveq1i
    wph
    @48
    @95
    @68
    wph
    @95
    @48
    wph
    @48
    wph
    @48
    @61
    nn0cnd
    addid2d
    eqcomd
    fveq2d
    syl5eq
    wph
    @60
    @70
    cc0
    cc0
    @66
    cfzo
    co
    wcel
    #
    @96
    @97
    wceq
    pgpfac.2
    @71
    wph
    @66
    cn
    wcel
    @98
    wph
    @66
    c1
    cn
    @72
    c1
    cn
    wcel
    wph
    1nn
    a1i
    syl5eqel
    @66
    lbfzo0
    sylibr
    cC
    cS
    @65
    cc0
    ccatval3
    syl3anc
    @12
    cvv
    wcel
    @97
    @12
    wceq
    wph
    @11
    cK
    fvex
    @12
    cvv
    s1fv
    mp1i
    3eqtrd
    opeq2d
    sneqd
    eqtrd
    #
    breqtrrd
    #
    wph
    cG
    @77
    cdprd
    co
    #
    cG
    @85
    cdprd
    co
    #
    cG
    @54
    @75
    pgpfac.g
    wph
    cG
    @77
    @2
    wbr
    @101
    @13
    wcel
    @84
    @77
    cG
    dprdsubg
    syl
    #
    wph
    cG
    @85
    @2
    wbr
    @102
    @13
    wcel
    @100
    @85
    cG
    dprdsubg
    syl
    ablcntzd
    wph
    @12
    cW
    cin
    #
    c.0
    csn
    @101
    @102
    cin
    #
    @53
    csn
    pgpfac.i
    wph
    @105
    cW
    @12
    cin
    @104
    wph
    @101
    cW
    @102
    @12
    wph
    @101
    cG
    cS
    cdprd
    co
    cW
    wph
    @77
    cS
    cG
    cdprd
    @83
    oveq2d
    pgpfac.5
    eqtrd
    #
    wph
    @102
    @87
    @12
    wph
    @85
    @79
    cG
    cdprd
    @99
    oveq2d
    wph
    @86
    @88
    @90
    simprd
    eqtrd
    #
    ineq12d
    cW
    @12
    incom
    syl6eq
    wph
    @53
    c.0
    wph
    @53
    cH
    c0g
    cfv
    #
    c.0
    wph
    @28
    @53
    @108
    wceq
    pgpfac.u
    cU
    cG
    cH
    @53
    pgpfac.h
    @76
    subg0
    syl
    pgpfac.0
    syl6eqr
    sneqd
    3eqtr4d
    dmdprdsplit2
    #
    wph
    @4
    @12
    cW
    cG
    clsm
    cfv
    #
    co
    #
    @12
    cW
    c.po
    co
    #
    cU
    wph
    @4
    @101
    @102
    @110
    co
    cW
    @12
    @110
    co
    #
    @111
    wph
    @49
    @50
    @110
    cT
    cG
    @52
    @57
    @62
    @74
    @110
    eqid
    #
    @109
    dprdsplit
    wph
    @101
    cW
    @102
    @12
    @110
    @106
    @107
    oveq12d
    wph
    cG
    cabl
    wcel
    cW
    @13
    wcel
    @14
    @113
    @111
    wceq
    pgpfac.g
    wph
    @101
    cW
    @13
    @106
    @103
    eqeltrrd
    @34
    @110
    cW
    @12
    cG
    @114
    lsmcom
    syl3anc
    3eqtrd
    wph
    @28
    @20
    cW
    cU
    wss
    @111
    @112
    wceq
    pgpfac.u
    @38
    wph
    cW
    @24
    cU
    wph
    cW
    @21
    wcel
    cW
    @24
    wss
    pgpfac.w
    @24
    cW
    cH
    @30
    subgss
    syl
    @31
    sseqtr4d
    c.po
    @110
    cU
    @12
    cW
    cG
    cH
    pgpfac.h
    @114
    pgpfac.l
    subglsm
    syl3anc
    pgpfac.s
    3eqtrd
    @10
    @3
    @5
    wa
    vs
    cT
    @0
    @6
    cT
    wceq
    #
    @7
    @3
    @9
    @5
    @6
    cT
    cG
    @2
    breq2
    @115
    @8
    @4
    cU
    @6
    cT
    cG
    cdprd
    oveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
end
