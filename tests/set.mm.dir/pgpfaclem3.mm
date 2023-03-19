include "cv.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cword.mm"
include "wrex.mm"
include "cress.mm"
include "cgex.mm"
include "cfv.mm"
include "c1.mm"
include "c0.mm"
include "wcel.mm"
include "wrd0.mm"
include "c0g.mm"
include "csn.mm"
include "cabl.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "eqid.mm"
include "dprd0.mm"
include "3syl.mm"
include "adantr.mm"
include "c1o.mm"
include "cen.mm"
include "csubg.mm"
include "subg0cl.mm"
include "syl.mm"
include "cbs.mm"
include "subgbas.mm"
include "cmnd.mm"
include "wb.mm"
include "subggrp.mm"
include "grpmnd.mm"
include "gex1.mm"
include "biimpa.mm"
include "eqbrtrd.mm"
include "en1eqsn.mm"
include "syl2anc.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "mpbird.mm"
include "breq2.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "wne.mm"
include "cod.mm"
include "cn.mm"
include "subgabl.mm"
include "cfn.mm"
include "wss.mm"
include "subgss.mm"
include "ssfi.mm"
include "eqeltrrd.mm"
include "gexcl2.mm"
include "gexex.mm"
include "cmrc.mm"
include "cin.mm"
include "clsm.mm"
include "cpgp.mm"
include "subgpgp.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "simprl.mm"
include "pgpfac1.mm"
include "ad3antrrr.mm"
include "wpss.mm"
include "wi.mm"
include "wral.mm"
include "simpllr.mm"
include "simplrl.mm"
include "eleqtrrd.mm"
include "simplrr.mm"
include "simprrl.mm"
include "simprrr.mm"
include "eqtr4d.mm"
include "pgpfaclem2.mm"
include "rexlimddv.mm"
include "pm2.61dane.mm"

theorem pgpfaclem3
  let wph: wff ph
  let vt: setvar t
  let cB: class B
  let cC: class C
  let cP: class P
  let cU: class U
  let cG: class G
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let cK: class K
  let cW: class W
  let cX: class X
  let cT: class T
  assume pgpfac.b: |- B = ( Base ` G )
  assume pgpfac.c: |- C = { r e. ( SubGrp ` G ) | ( G |`s r ) e. ( CycGrp i^i ran pGrp ) }
  assume pgpfac.g: |- ( ph -> G e. Abel )
  assume pgpfac.p: |- ( ph -> P pGrp G )
  assume pgpfac.f: |- ( ph -> B e. Fin )
  assume pgpfac.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume pgpfac.a: |- ( ph -> A. t e. ( SubGrp ` G ) ( t C. U -> E. s e. Word C ( G dom DProd s /\ ( G DProd s ) = t ) ) )

  disjoint s t
  disjoint C s
  disjoint C t
  disjoint r s
  disjoint r t
  disjoint G r
  disjoint G s
  disjoint G t
  disjoint ph t
  disjoint B s
  disjoint B t
  disjoint U r
  disjoint U s
  disjoint U t
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
  disjoint K r
  disjoint K s
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
  disjoint W s
  disjoint W t
  disjoint X r
  disjoint X s
  disjoint T s
  assert |- ( ph -> E. s e. Word C ( G dom DProd s /\ ( G DProd s ) = U ) )

  proof
    wph
    cG
    vs
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
    cU
    wceq
    #
    wa
    #
    vs
    cC
    cword
    #
    wrex
    #
    cG
    cU
    cress
    co
    #
    cgex
    cfv
    #
    c1
    wph
    @9
    c1
    wceq
    #
    wa
    #
    c0
    @6
    wcel
    cG
    c0
    @1
    wbr
    #
    cG
    c0
    cdprd
    co
    #
    cU
    wceq
    #
    wa
    #
    @7
    cC
    wrd0
    @11
    @15
    @12
    @13
    cG
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    wa
    #
    wph
    @19
    @10
    wph
    cG
    cabl
    wcel
    #
    cG
    cgrp
    wcel
    @19
    pgpfac.g
    cG
    ablgrp
    cG
    @16
    @16
    eqid
    #
    dprd0
    3syl
    adantr
    @11
    @14
    @18
    @12
    @11
    cU
    @17
    @13
    @11
    @16
    cU
    wcel
    #
    cU
    c1o
    cen
    wbr
    cU
    @17
    wceq
    wph
    @22
    @10
    wph
    cU
    cG
    csubg
    cfv
    #
    wcel
    #
    @22
    pgpfac.u
    cU
    cG
    @16
    @21
    subg0cl
    syl
    adantr
    @11
    cU
    @8
    cbs
    cfv
    #
    c1o
    cen
    wph
    cU
    @25
    wceq
    #
    @10
    wph
    @24
    @26
    pgpfac.u
    cU
    cG
    @8
    @8
    eqid
    #
    subgbas
    #
    syl
    #
    adantr
    wph
    @10
    @25
    c1o
    cen
    wbr
    #
    wph
    @8
    cgrp
    wcel
    #
    @8
    cmnd
    wcel
    @10
    @30
    wb
    wph
    @24
    @31
    pgpfac.u
    cU
    cG
    @8
    @27
    subggrp
    syl
    #
    @8
    grpmnd
    @9
    @8
    @25
    @25
    eqid
    #
    @9
    eqid
    #
    gex1
    3syl
    biimpa
    eqbrtrd
    @16
    cU
    en1eqsn
    syl2anc
    eqeq2d
    anbi2d
    mpbird
    @5
    @15
    vs
    c0
    @6
    @0
    c0
    wceq
    #
    @2
    @12
    @4
    @14
    @0
    c0
    cG
    @1
    breq2
    @35
    @3
    @13
    cU
    @0
    c0
    cG
    cdprd
    oveq2
    eqeq1d
    anbi12d
    rspcev
    sylancr
    wph
    @9
    c1
    wne
    #
    wa
    #
    vx
    cv
    #
    @8
    cod
    cfv
    #
    cfv
    @9
    wceq
    #
    @7
    vx
    @25
    wph
    @40
    vx
    @25
    wrex
    #
    @36
    wph
    @8
    cabl
    wcel
    #
    @9
    cn
    wcel
    #
    @41
    wph
    @20
    @24
    @42
    pgpfac.g
    pgpfac.u
    cU
    cG
    @8
    @27
    subgabl
    syl2anc
    #
    wph
    @31
    @25
    cfn
    wcel
    #
    @43
    @32
    wph
    cU
    @25
    cfn
    @29
    wph
    cB
    cfn
    wcel
    #
    cU
    cB
    wss
    #
    cU
    cfn
    wcel
    pgpfac.f
    wph
    @24
    @47
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
    eqeltrrd
    #
    @9
    @8
    @25
    @33
    @34
    gexcl2
    syl2anc
    vx
    @9
    @8
    @39
    @25
    @33
    @34
    @39
    eqid
    #
    gexex
    syl2anc
    adantr
    @37
    @38
    @25
    wcel
    #
    @40
    wa
    #
    wa
    #
    @38
    csn
    @8
    csubg
    cfv
    #
    cmrc
    cfv
    #
    cfv
    #
    vw
    cv
    #
    cin
    @8
    c0g
    cfv
    #
    csn
    wceq
    #
    @55
    @56
    @8
    clsm
    cfv
    #
    co
    #
    @25
    wceq
    #
    wa
    #
    @7
    vw
    @53
    @52
    vw
    @38
    @25
    cP
    @59
    @55
    @9
    @8
    @54
    @39
    @57
    @54
    eqid
    #
    @55
    eqid
    @33
    @49
    @34
    @57
    eqid
    #
    @59
    eqid
    #
    wph
    cP
    @8
    cpgp
    wbr
    #
    @36
    @51
    wph
    cP
    cG
    cpgp
    wbr
    #
    @24
    @66
    pgpfac.p
    pgpfac.u
    cP
    cU
    cG
    subgpgp
    syl2anc
    ad2antrr
    wph
    @42
    @36
    @51
    @44
    ad2antrr
    wph
    @45
    @36
    @51
    @48
    ad2antrr
    @37
    @50
    @40
    simprr
    @37
    @50
    @40
    simprl
    pgpfac1
    @52
    @56
    @53
    wcel
    #
    @62
    wa
    #
    wa
    #
    vt
    cB
    cC
    cP
    @59
    cU
    @9
    cG
    @8
    @54
    @39
    @56
    @38
    @57
    vs
    vr
    pgpfac.b
    pgpfac.c
    wph
    @20
    @36
    @51
    @69
    pgpfac.g
    ad3antrrr
    wph
    @67
    @36
    @51
    @69
    pgpfac.p
    ad3antrrr
    wph
    @46
    @36
    @51
    @69
    pgpfac.f
    ad3antrrr
    wph
    @24
    @36
    @51
    @69
    pgpfac.u
    ad3antrrr
    #
    wph
    vt
    cv
    #
    cU
    wpss
    @2
    @3
    @72
    wceq
    wa
    vs
    @6
    wrex
    wi
    vt
    @23
    wral
    @36
    @51
    @69
    pgpfac.a
    ad3antrrr
    @27
    @63
    @49
    @34
    @64
    @65
    wph
    @36
    @51
    @69
    simpllr
    @70
    @38
    @25
    cU
    @37
    @50
    @40
    @69
    simplrl
    @70
    @24
    @26
    @71
    @28
    syl
    #
    eleqtrrd
    @37
    @50
    @40
    @69
    simplrr
    @52
    @68
    @62
    simprl
    @52
    @68
    @58
    @61
    simprrl
    @70
    @60
    @25
    cU
    @52
    @68
    @58
    @61
    simprrr
    @73
    eqtr4d
    pgpfaclem2
    rexlimddv
    rexlimddv
    pm2.61dane
end
