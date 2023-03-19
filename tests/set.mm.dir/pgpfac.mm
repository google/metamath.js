include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cword.mm"
include "wrex.mm"
include "cabl.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "subgid.mm"
include "3syl.mm"
include "cfn.mm"
include "wi.mm"
include "eleq1.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wpss.mm"
include "wal.mm"
include "wral.mm"
include "bi2.04.mm"
include "imbi2i.mm"
include "3bitr4i.mm"
include "albii.mm"
include "df-ral.mm"
include "r19.21v.mm"
include "3bitr2i.mm"
include "adantr.mm"
include "cpgp.mm"
include "simprr.mm"
include "simprl.mm"
include "psseq1.mm"
include "cbvralv.mm"
include "sylib.mm"
include "pgpfaclem3.mm"
include "exp32.mm"
include "a1i.mm"
include "a2d.mm"
include "syl5bi.mm"
include "findcard3.mm"
include "mpcom.mm"
include "mpd.mm"

theorem pgpfac
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let cK: class K
  let cU: class U
  let cW: class W
  let cX: class X
  let cT: class T
  assume pgpfac.b: |- B = ( Base ` G )
  assume pgpfac.c: |- C = { r e. ( SubGrp ` G ) | ( G |`s r ) e. ( CycGrp i^i ran pGrp ) }
  assume pgpfac.g: |- ( ph -> G e. Abel )
  assume pgpfac.p: |- ( ph -> P pGrp G )
  assume pgpfac.f: |- ( ph -> B e. Fin )

  disjoint C s
  disjoint r s
  disjoint G r
  disjoint G s
  disjoint B s
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a w
  disjoint a x
  disjoint C a
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint C t
  disjoint u w
  disjoint u x
  disjoint C u
  disjoint w x
  disjoint C w
  disjoint C x
  disjoint a r
  disjoint G a
  disjoint r t
  disjoint r u
  disjoint r w
  disjoint r x
  disjoint G t
  disjoint G u
  disjoint G w
  disjoint G x
  disjoint K r
  disjoint K s
  disjoint a ph
  disjoint ph t
  disjoint ph u
  disjoint ph w
  disjoint ph x
  disjoint B t
  disjoint B x
  disjoint P w
  disjoint U a
  disjoint U r
  disjoint U s
  disjoint U t
  disjoint U w
  disjoint U x
  disjoint W a
  disjoint W s
  disjoint W t
  disjoint X r
  disjoint X s
  disjoint T s
  assert |- ( ph -> E. s e. Word C ( G dom DProd s /\ ( G DProd s ) = B ) )

  proof
    wph
    cB
    cG
    csubg
    cfv
    #
    wcel
    #
    cG
    vs
    cv
    #
    cdprd
    cdm
    wbr
    #
    cG
    @2
    cdprd
    co
    #
    cB
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
    wph
    cG
    cabl
    wcel
    #
    cG
    cgrp
    wcel
    @1
    pgpfac.g
    cG
    ablgrp
    cB
    cG
    pgpfac.b
    subgid
    3syl
    cB
    cfn
    wcel
    #
    wph
    @1
    @8
    wi
    #
    pgpfac.f
    wph
    vt
    cv
    #
    @0
    wcel
    #
    @3
    @4
    @12
    wceq
    #
    wa
    #
    vs
    @7
    wrex
    #
    wi
    #
    wi
    #
    wph
    vu
    cv
    #
    @0
    wcel
    #
    @3
    @4
    @19
    wceq
    #
    wa
    #
    vs
    @7
    wrex
    #
    wi
    #
    wi
    #
    wph
    @11
    wi
    vt
    vu
    cB
    @12
    @19
    wceq
    #
    @17
    @24
    wph
    @26
    @13
    @20
    @16
    @23
    @12
    @19
    @0
    eleq1
    @26
    @15
    @22
    vs
    @7
    @26
    @14
    @21
    @3
    @12
    @19
    @4
    eqeq2
    anbi2d
    rexbidv
    imbi12d
    imbi2d
    @12
    cB
    wceq
    #
    @17
    @11
    wph
    @27
    @13
    @1
    @16
    @8
    @12
    cB
    @0
    eleq1
    @27
    @15
    @6
    vs
    @7
    @27
    @14
    @5
    @3
    @12
    cB
    @4
    eqeq2
    anbi2d
    rexbidv
    imbi12d
    imbi2d
    @12
    @19
    wpss
    #
    @18
    wi
    #
    vt
    wal
    #
    wph
    @28
    @16
    wi
    #
    vt
    @0
    wral
    #
    wi
    #
    @19
    cfn
    wcel
    #
    @25
    @30
    @13
    wph
    @31
    wi
    #
    wi
    #
    vt
    wal
    @35
    vt
    @0
    wral
    @33
    @29
    @36
    vt
    wph
    @28
    @17
    wi
    #
    wi
    wph
    @13
    @31
    wi
    #
    wi
    @29
    @36
    @37
    @38
    wph
    @28
    @13
    @16
    bi2.04
    imbi2i
    @28
    wph
    @17
    bi2.04
    @13
    wph
    @31
    bi2.04
    3bitr4i
    albii
    @35
    vt
    @0
    df-ral
    wph
    @31
    vt
    @0
    r19.21v
    3bitr2i
    @34
    wph
    @32
    @24
    wph
    @32
    @24
    wi
    wi
    @34
    wph
    @32
    @20
    @23
    wph
    @32
    @20
    wa
    #
    wa
    #
    vx
    cB
    cC
    cP
    @19
    cG
    vs
    vr
    pgpfac.b
    pgpfac.c
    wph
    @9
    @39
    pgpfac.g
    adantr
    wph
    cP
    cG
    cpgp
    wbr
    @39
    pgpfac.p
    adantr
    wph
    @10
    @39
    pgpfac.f
    adantr
    wph
    @32
    @20
    simprr
    @40
    @32
    vx
    cv
    #
    @19
    wpss
    #
    @3
    @4
    @41
    wceq
    #
    wa
    #
    vs
    @7
    wrex
    #
    wi
    #
    vx
    @0
    wral
    wph
    @32
    @20
    simprl
    @31
    @46
    vt
    vx
    @0
    @12
    @41
    wceq
    #
    @28
    @42
    @16
    @45
    @12
    @41
    @19
    psseq1
    @47
    @15
    @44
    vs
    @7
    @47
    @14
    @43
    @3
    @12
    @41
    @4
    eqeq2
    anbi2d
    rexbidv
    imbi12d
    cbvralv
    sylib
    pgpfaclem3
    exp32
    a1i
    a2d
    syl5bi
    findcard3
    mpcom
    mpd
end
