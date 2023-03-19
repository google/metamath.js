include "cv.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cword.mm"
include "wrex.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wpss.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "wb.mm"
include "subsubg.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "wne.mm"
include "simprd.mm"
include "chash.mm"
include "cfn.mm"
include "cn0.mm"
include "subgss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "hashcl.mm"
include "nn0red.mm"
include "c1.mm"
include "cmul.mm"
include "csn.mm"
include "clt.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "csdm.mm"
include "cbs.mm"
include "cgrp.mm"
include "cacs.mm"
include "cmre.mm"
include "subgrcl.mm"
include "eqid.mm"
include "subgacs.mm"
include "acsmre.mm"
include "4syl.mm"
include "mrcssvd.mm"
include "subgbas.mm"
include "sseqtr4d.mm"
include "eleqtrd.mm"
include "mrcsncl.mm"
include "subg0cl.mm"
include "snssd.mm"
include "mrcssidd.mm"
include "snssg.mm"
include "mpbird.mm"
include "wn.mm"
include "eqnetrd.mm"
include "od1.mm"
include "3syl.mm"
include "elsni.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3ad.mm"
include "mpd.mm"
include "ssnelpssd.mm"
include "php3.mm"
include "snfi.mm"
include "hashsdom.mm"
include "sylancr.mm"
include "syl5eqbrr.mm"
include "cr.mm"
include "cc0.mm"
include "1red.mm"
include "cn.mm"
include "c0.mm"
include "ne0i.mm"
include "hashnncl.mm"
include "nngt0d.mm"
include "ltmul1.mm"
include "syl112anc.mm"
include "recnd.mm"
include "mulid2d.mm"
include "ccntz.mm"
include "cabl.mm"
include "subgabl.mm"
include "ablcntzd.mm"
include "lsmhash.mm"
include "eqtr3d.mm"
include "3brtr3d.mm"
include "ltned.mm"
include "fveq2.mm"
include "necon3i.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "psseq1.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "breq2.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "cs1.mm"
include "cconcat.mm"
include "adantr.mm"
include "cpgp.mm"
include "cin.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "pgpfaclem1.mm"
include "rexlimddv.mm"

theorem pgpfaclem2
  let wph: wff ph
  let vt: setvar t
  let cB: class B
  let cC: class C
  let cP: class P
  let c.po: class .(+)
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
  let cT: class T
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
  disjoint T s
  assert |- ( ph -> E. s e. Word C ( G dom DProd s /\ ( G DProd s ) = U ) )

  proof
    wph
    cG
    va
    cv
    #
    cdprd
    cdm
    #
    wbr
    #
    cG
    @0
    cdprd
    co
    #
    cW
    wceq
    #
    wa
    #
    cG
    vs
    cv
    #
    @1
    wbr
    #
    cG
    @6
    cdprd
    co
    #
    cU
    wceq
    wa
    vs
    cC
    cword
    #
    wrex
    va
    @9
    wph
    @7
    @8
    cW
    wceq
    #
    wa
    #
    vs
    @9
    wrex
    #
    @5
    va
    @9
    wrex
    wph
    cW
    cG
    csubg
    cfv
    #
    wcel
    #
    vt
    cv
    #
    cU
    wpss
    #
    @7
    @8
    @15
    wceq
    #
    wa
    #
    vs
    @9
    wrex
    #
    wi
    #
    vt
    @13
    wral
    #
    cW
    cU
    wpss
    #
    @12
    wph
    @14
    cW
    cU
    wss
    #
    wph
    cW
    cH
    csubg
    cfv
    #
    wcel
    #
    @14
    @23
    wa
    #
    pgpfac.w
    wph
    cU
    @13
    wcel
    #
    @25
    @26
    wb
    pgpfac.u
    cW
    cU
    cG
    cH
    pgpfac.h
    subsubg
    syl
    mpbid
    #
    simpld
    pgpfac.a
    wph
    @23
    cW
    cU
    wne
    #
    @22
    wph
    @14
    @23
    @28
    simprd
    #
    wph
    cW
    chash
    cfv
    #
    cU
    chash
    cfv
    #
    wne
    @29
    wph
    @31
    @32
    wph
    @31
    wph
    cW
    cfn
    wcel
    #
    @31
    cn0
    wcel
    wph
    cU
    cfn
    wcel
    #
    @23
    @33
    wph
    cB
    cfn
    wcel
    #
    cU
    cB
    wss
    #
    @34
    pgpfac.f
    wph
    @27
    @36
    pgpfac.u
    cB
    cU
    cG
    pgpfac.b
    subgss
    syl
    cB
    cU
    ssfi
    syl2anc
    #
    @30
    cU
    cW
    ssfi
    syl2anc
    #
    cW
    hashcl
    syl
    nn0red
    #
    wph
    c1
    @31
    cmul
    co
    #
    cX
    csn
    #
    cK
    cfv
    #
    chash
    cfv
    #
    @31
    cmul
    co
    #
    @31
    @32
    clt
    wph
    c1
    @43
    clt
    wbr
    #
    @40
    @44
    clt
    wbr
    #
    wph
    c1
    c.0
    csn
    #
    chash
    cfv
    #
    @43
    clt
    c.0
    cvv
    wcel
    @48
    c1
    wceq
    c.0
    cH
    c0g
    cfv
    cvv
    pgpfac.0
    cH
    c0g
    fvex
    eqeltri
    c.0
    cvv
    hashsng
    ax-mp
    wph
    @48
    @43
    clt
    wbr
    #
    @47
    @42
    csdm
    wbr
    #
    wph
    @42
    cfn
    wcel
    #
    @47
    @42
    wpss
    @50
    wph
    @34
    @42
    cU
    wss
    @51
    @37
    wph
    @42
    cH
    cbs
    cfv
    #
    cU
    wph
    @24
    @41
    cK
    @52
    wph
    @25
    cH
    cgrp
    wcel
    #
    @24
    @52
    cacs
    cfv
    wcel
    @24
    @52
    cmre
    cfv
    wcel
    #
    pgpfac.w
    cW
    cH
    subgrcl
    #
    @52
    cH
    @52
    eqid
    subgacs
    @24
    @52
    acsmre
    4syl
    #
    pgpfac.k
    mrcssvd
    wph
    @27
    cU
    @52
    wceq
    pgpfac.u
    cU
    cG
    cH
    pgpfac.h
    subgbas
    syl
    #
    sseqtr4d
    cU
    @42
    ssfi
    syl2anc
    #
    wph
    @47
    @42
    cX
    wph
    c.0
    @42
    wph
    @42
    @24
    wcel
    #
    c.0
    @42
    wcel
    wph
    @54
    cX
    @52
    wcel
    @59
    @56
    wph
    cX
    cU
    @52
    pgpfac.x
    @57
    eleqtrd
    #
    @24
    cX
    cK
    @52
    pgpfac.k
    mrcsncl
    syl2anc
    #
    @42
    cH
    c.0
    pgpfac.0
    subg0cl
    syl
    snssd
    wph
    cX
    @42
    wcel
    #
    @41
    @42
    wss
    #
    wph
    @24
    @41
    cK
    @52
    @56
    pgpfac.k
    wph
    cX
    @52
    @60
    snssd
    mrcssidd
    wph
    cX
    cU
    wcel
    #
    @62
    @63
    wb
    pgpfac.x
    cX
    @42
    cU
    snssg
    syl
    mpbird
    wph
    cX
    cO
    cfv
    #
    c1
    wne
    cX
    @47
    wcel
    #
    wn
    wph
    @65
    cE
    c1
    pgpfac.oe
    pgpfac.1
    eqnetrd
    wph
    @66
    @65
    c1
    wph
    @65
    c1
    wceq
    @66
    c.0
    cO
    cfv
    #
    c1
    wceq
    #
    wph
    @25
    @53
    @68
    pgpfac.w
    @55
    cH
    cO
    c.0
    pgpfac.o
    pgpfac.0
    od1
    3syl
    @66
    @65
    @67
    c1
    @66
    cX
    c.0
    cO
    cX
    c.0
    elsni
    fveq2d
    eqeq1d
    syl5ibrcom
    necon3ad
    mpd
    ssnelpssd
    @42
    @47
    php3
    syl2anc
    wph
    @47
    cfn
    wcel
    @51
    @49
    @50
    wb
    c.0
    snfi
    @58
    @47
    @42
    hashsdom
    sylancr
    mpbird
    syl5eqbrr
    wph
    c1
    cr
    wcel
    @43
    cr
    wcel
    @31
    cr
    wcel
    cc0
    @31
    clt
    wbr
    @45
    @46
    wb
    wph
    1red
    wph
    @43
    wph
    @51
    @43
    cn0
    wcel
    @58
    @42
    hashcl
    syl
    nn0red
    @39
    wph
    @31
    wph
    @31
    cn
    wcel
    #
    cW
    c0
    wne
    #
    wph
    @25
    c.0
    cW
    wcel
    @70
    pgpfac.w
    cW
    cH
    c.0
    pgpfac.0
    subg0cl
    cW
    c.0
    ne0i
    3syl
    wph
    @33
    @69
    @70
    wb
    @38
    cW
    hashnncl
    syl
    mpbird
    nngt0d
    c1
    @43
    @31
    ltmul1
    syl112anc
    mpbid
    wph
    @31
    wph
    @31
    @39
    recnd
    mulid2d
    wph
    @42
    cW
    c.po
    co
    #
    chash
    cfv
    @44
    @32
    wph
    c.po
    @42
    cW
    cH
    c.0
    cH
    ccntz
    cfv
    #
    pgpfac.l
    pgpfac.0
    @72
    eqid
    #
    @61
    pgpfac.w
    pgpfac.i
    wph
    @42
    cW
    cH
    @72
    @73
    wph
    cG
    cabl
    wcel
    #
    @27
    cH
    cabl
    wcel
    pgpfac.g
    pgpfac.u
    cU
    cG
    cH
    pgpfac.h
    subgabl
    syl2anc
    @61
    pgpfac.w
    ablcntzd
    @58
    @38
    lsmhash
    wph
    @71
    cU
    chash
    pgpfac.s
    fveq2d
    eqtr3d
    3brtr3d
    ltned
    cW
    cU
    @31
    @32
    cW
    cU
    chash
    fveq2
    necon3i
    syl
    cW
    cU
    df-pss
    sylanbrc
    @20
    @22
    @12
    wi
    vt
    cW
    @13
    @15
    cW
    wceq
    #
    @16
    @22
    @19
    @12
    @15
    cW
    cU
    psseq1
    @75
    @18
    @11
    vs
    @9
    @75
    @17
    @10
    @7
    @15
    cW
    @8
    eqeq2
    anbi2d
    rexbidv
    imbi12d
    rspcv
    syl3c
    @11
    @5
    vs
    va
    @9
    @6
    @0
    wceq
    #
    @7
    @2
    @10
    @4
    @6
    @0
    cG
    @1
    breq2
    @76
    @8
    @3
    cW
    @6
    @0
    cG
    cdprd
    oveq2
    eqeq1d
    anbi12d
    cbvrexv
    sylib
    wph
    @0
    @9
    wcel
    #
    @5
    wa
    #
    wa
    vt
    cB
    cC
    cP
    c.po
    @0
    @0
    @42
    cs1
    cconcat
    co
    #
    cU
    cE
    cG
    cH
    cK
    cO
    cW
    cX
    c.0
    vs
    vr
    pgpfac.b
    pgpfac.c
    wph
    @74
    @78
    pgpfac.g
    adantr
    wph
    cP
    cG
    cpgp
    wbr
    @78
    pgpfac.p
    adantr
    wph
    @35
    @78
    pgpfac.f
    adantr
    wph
    @27
    @78
    pgpfac.u
    adantr
    wph
    @21
    @78
    pgpfac.a
    adantr
    pgpfac.h
    pgpfac.k
    pgpfac.o
    pgpfac.e
    pgpfac.0
    pgpfac.l
    wph
    cE
    c1
    wne
    @78
    pgpfac.1
    adantr
    wph
    @64
    @78
    pgpfac.x
    adantr
    wph
    @65
    cE
    wceq
    @78
    pgpfac.oe
    adantr
    wph
    @25
    @78
    pgpfac.w
    adantr
    wph
    @42
    cW
    cin
    @47
    wceq
    @78
    pgpfac.i
    adantr
    wph
    @71
    cU
    wceq
    @78
    pgpfac.s
    adantr
    wph
    @77
    @5
    simprl
    wph
    @77
    @2
    @4
    simprrl
    wph
    @77
    @2
    @4
    simprrr
    @79
    eqid
    pgpfaclem1
    rexlimddv
end
