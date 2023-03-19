include "cgsu.mm"
include "co.mm"
include "cress.mm"
include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubmnd.mm"
include "subrgply1.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "subgsubm.mm"
include "syl.mm"
include "3syl.mm"
include "eqid.mm"
include "gsumsubm.mm"
include "cvv.mm"
include "wf.mm"
include "fex.mm"
include "syl2anc.mm"
include "ovexd.mm"
include "cpl1.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cbs.mm"
include "oveq2i.mm"
include "ressply1bas.mm"
include "eqcomd.mm"
include "crg.mm"
include "cmgm.mm"
include "subrgring.mm"
include "ringmgm.mm"
include "cv.mm"
include "wa.mm"
include "cplusg.mm"
include "wceq.mm"
include "simpl.mm"
include "wi.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "adantr.mm"
include "impcom.mm"
include "adantl.mm"
include "ressply1add.mm"
include "syl12anc.mm"
include "wfun.mm"
include "ffun.mm"
include "crn.mm"
include "wss.mm"
include "frn.mm"
include "sseqtrd.mm"
include "gsummgmpropd.mm"
include "eqtrd.mm"

theorem gsumply1subr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vs: setvar s
  let vt: setvar t
  assume subrgply1.s: |- S = ( Poly1 ` R )
  assume subrgply1.h: |- H = ( R |`s T )
  assume subrgply1.u: |- U = ( Poly1 ` H )
  assume subrgply1.b: |- B = ( Base ` U )
  assume gsumply1subr.s: |- ( ph -> T e. ( SubRing ` R ) )
  assume gsumply1subr.a: |- ( ph -> A e. V )
  assume gsumply1subr.f: |- ( ph -> F : A --> B )


  assert |- ( ph -> ( S gsum F ) = ( U gsum F ) )

  proof
    wph
    cS
    cF
    cgsu
    co
    cS
    cB
    cress
    co
    #
    cF
    cgsu
    co
    cU
    cF
    cgsu
    co
    wph
    cA
    cB
    cF
    cS
    @0
    cV
    gsumply1subr.a
    wph
    cT
    cR
    csubrg
    cfv
    wcel
    #
    cB
    cS
    csubrg
    cfv
    wcel
    #
    cB
    cS
    csubmnd
    cfv
    wcel
    #
    gsumply1subr.s
    cB
    cR
    cS
    cT
    cU
    cH
    subrgply1.s
    subrgply1.h
    subrgply1.u
    subrgply1.b
    subrgply1
    #
    @2
    cB
    cS
    csubg
    cfv
    wcel
    @3
    cB
    cS
    subrgsubg
    cB
    cS
    subgsubm
    syl
    3syl
    gsumply1subr.f
    @0
    eqid
    #
    gsumsubm
    wph
    vt
    cF
    @0
    cU
    cvv
    cvv
    cvv
    vs
    wph
    cA
    cB
    cF
    wf
    #
    cA
    cV
    wcel
    cF
    cvv
    wcel
    gsumply1subr.f
    gsumply1subr.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    wph
    cS
    cB
    cress
    ovexd
    cU
    cvv
    wcel
    wph
    cU
    cH
    cpl1
    cfv
    cvv
    subrgply1.u
    cH
    cpl1
    fvex
    eqeltri
    a1i
    wph
    cU
    cbs
    cfv
    #
    @0
    cbs
    cfv
    #
    wph
    @7
    @0
    cR
    cS
    cT
    cU
    cH
    subrgply1.s
    subrgply1.h
    subrgply1.u
    @7
    eqid
    gsumply1subr.s
    cB
    @7
    cS
    cress
    subrgply1.b
    oveq2i
    ressply1bas
    eqcomd
    wph
    @1
    @0
    crg
    wcel
    #
    @0
    cmgm
    wcel
    gsumply1subr.s
    @1
    @2
    @9
    @4
    cB
    cS
    @0
    @5
    subrgring
    syl
    @0
    ringmgm
    3syl
    wph
    vs
    cv
    #
    @8
    wcel
    #
    vt
    cv
    #
    @8
    wcel
    #
    wa
    #
    wa
    #
    @10
    @12
    cU
    cplusg
    cfv
    co
    #
    @10
    @12
    @0
    cplusg
    cfv
    co
    #
    @15
    wph
    @10
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @16
    @17
    wceq
    wph
    @14
    simpl
    @14
    wph
    @18
    @11
    wph
    @18
    wi
    @13
    wph
    @11
    @18
    wph
    @8
    cB
    @10
    wph
    cB
    @8
    wph
    cB
    @0
    cR
    cS
    cT
    cU
    cH
    subrgply1.s
    subrgply1.h
    subrgply1.u
    subrgply1.b
    gsumply1subr.s
    @5
    ressply1bas
    #
    eqcomd
    #
    eleq2d
    biimpcd
    adantr
    impcom
    @14
    wph
    @19
    @13
    wph
    @19
    wi
    @11
    wph
    @13
    @19
    wph
    @8
    cB
    @12
    @21
    eleq2d
    biimpcd
    adantl
    impcom
    wph
    cB
    @0
    cR
    cS
    cT
    cU
    cH
    @10
    @12
    subrgply1.s
    subrgply1.h
    subrgply1.u
    subrgply1.b
    gsumply1subr.s
    @5
    ressply1add
    syl12anc
    eqcomd
    wph
    @6
    cF
    wfun
    gsumply1subr.f
    cA
    cB
    cF
    ffun
    syl
    wph
    cF
    crn
    #
    cB
    @8
    wph
    @6
    @22
    cB
    wss
    gsumply1subr.f
    cA
    cB
    cF
    frn
    syl
    @20
    sseqtrd
    gsummgmpropd
    eqtrd
end
