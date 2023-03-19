include "cres.mm"
include "wfn.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "asclfn.mm"
include "csubrg.mm"
include "wcel.mm"
include "wceq.mm"
include "subrgbas.mm"
include "syl.mm"
include "cvv.mm"
include "cress.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "fneq2d.mm"
include "mpbiri.mm"
include "wss.mm"
include "crg.mm"
include "subrgrcl.mm"
include "subrgss.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "cv.mm"
include "wa.mm"
include "fvres.mm"
include "adantl.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt.mm"
include "subrg0.mm"
include "ifeq2d.mm"
include "adantr.mm"
include "mpteq2dv.mm"
include "sselda.mm"
include "mplascl.mm"
include "subrgring.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "3eqtr4d.mm"
include "eqtr2d.mm"
include "eqfnfvd.mm"

theorem subrgascl
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cW: class W
  let vx: setvar x
  let vf: setvar f
  let vy: setvar y
  let cK: class K
  let cX: class X
  assume subrgascl.p: |- P = ( I mPoly R )
  assume subrgascl.a: |- A = ( algSc ` P )
  assume subrgascl.h: |- H = ( R |`s T )
  assume subrgascl.u: |- U = ( I mPoly H )
  assume subrgascl.i: |- ( ph -> I e. W )
  assume subrgascl.r: |- ( ph -> T e. ( SubRing ` R ) )
  assume subrgascl.c: |- C = ( algSc ` U )


  assert |- ( ph -> C = ( A |` T ) )

  proof
    wph
    vx
    cT
    cC
    cA
    cT
    cres
    #
    wph
    cC
    cT
    wfn
    cC
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    wfn
    cC
    @1
    @2
    cU
    subrgascl.c
    @1
    eqid
    @2
    eqid
    asclfn
    wph
    cT
    @2
    cC
    wph
    cT
    cH
    cbs
    cfv
    #
    @2
    wph
    cT
    cR
    csubrg
    cfv
    wcel
    #
    cT
    @3
    wceq
    subrgascl.r
    cT
    cR
    cH
    subrgascl.h
    subrgbas
    syl
    #
    wph
    cH
    @1
    cbs
    wph
    cU
    cH
    cI
    cW
    cvv
    subrgascl.u
    subrgascl.i
    cH
    cvv
    wcel
    wph
    cH
    cR
    cT
    cress
    co
    cvv
    subrgascl.h
    cR
    cT
    cress
    ovex
    eqeltri
    a1i
    mplsca
    fveq2d
    eqtrd
    fneq2d
    mpbiri
    wph
    cA
    cR
    cbs
    cfv
    #
    wfn
    #
    cT
    @6
    wss
    #
    @0
    cT
    wfn
    wph
    @7
    cA
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wfn
    cA
    @9
    @10
    cP
    subrgascl.a
    @9
    eqid
    @10
    eqid
    asclfn
    wph
    @6
    @10
    cA
    wph
    cR
    @9
    cbs
    wph
    cP
    cR
    cI
    cW
    crg
    subrgascl.p
    subrgascl.i
    wph
    @4
    cR
    crg
    wcel
    #
    subrgascl.r
    cT
    cR
    subrgrcl
    syl
    #
    mplsca
    fveq2d
    fneq2d
    mpbiri
    wph
    @4
    @8
    subrgascl.r
    cT
    @6
    cR
    @6
    eqid
    #
    subrgss
    syl
    #
    @6
    cT
    cA
    fnssres
    syl2anc
    wph
    vx
    cv
    #
    cT
    wcel
    #
    wa
    #
    @15
    @0
    cfv
    #
    @15
    cA
    cfv
    #
    @15
    cC
    cfv
    #
    @16
    @18
    @19
    wceq
    wph
    @15
    cT
    cA
    fvres
    adantl
    @17
    vy
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    crab
    #
    vy
    cv
    cI
    cc0
    csn
    cxp
    wceq
    #
    @15
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt
    vy
    @21
    @22
    @15
    cH
    c0g
    cfv
    #
    cif
    #
    cmpt
    @19
    @20
    @17
    vy
    @21
    @24
    @26
    wph
    @24
    @26
    wceq
    @16
    wph
    @22
    @23
    @25
    @15
    wph
    @4
    @23
    @25
    wceq
    subrgascl.r
    cT
    cR
    cH
    @23
    subrgascl.h
    @23
    eqid
    #
    subrg0
    syl
    ifeq2d
    adantr
    mpteq2dv
    @17
    vy
    cA
    @6
    @21
    cP
    cR
    vf
    cI
    cW
    @15
    @23
    subrgascl.p
    @21
    eqid
    #
    @27
    @13
    subrgascl.a
    wph
    cI
    cW
    wcel
    @16
    subrgascl.i
    adantr
    #
    wph
    @11
    @16
    @12
    adantr
    wph
    cT
    @6
    @15
    @14
    sselda
    mplascl
    @17
    vy
    cC
    @3
    @21
    cU
    cH
    vf
    cI
    cW
    @15
    @25
    subrgascl.u
    @28
    @25
    eqid
    @3
    eqid
    subrgascl.c
    @29
    wph
    cH
    crg
    wcel
    #
    @16
    wph
    @4
    @30
    subrgascl.r
    cT
    cR
    cH
    subrgascl.h
    subrgring
    syl
    adantr
    wph
    @16
    @15
    @3
    wcel
    wph
    cT
    @3
    @15
    @5
    eleq2d
    biimpa
    mplascl
    3eqtr4d
    eqtr2d
    eqfnfvd
end
