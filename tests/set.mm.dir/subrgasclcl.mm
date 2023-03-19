include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "wceq.mm"
include "c0g.mm"
include "cif.mm"
include "wral.mm"
include "adantr.mm"
include "eqid.mm"
include "psrbag0.mm"
include "syl.mm"
include "cmpt.mm"
include "wf.mm"
include "cmps.mm"
include "csubrg.mm"
include "crg.mm"
include "subrgrcl.mm"
include "mplascl.mm"
include "wss.mm"
include "subrgring.mm"
include "mplsubrg.mm"
include "subrgss.mm"
include "sselda.mm"
include "eqeltrrd.mm"
include "psrelbas.mm"
include "fmpt.mm"
include "sylibr.mm"
include "iftrue.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "subrgbas.mm"
include "eleqtrrd.mm"
include "cascl.mm"
include "cres.mm"
include "subrgascl.mm"
include "fveq1d.mm"
include "fvres.mm"
include "sylan9eq.mm"
include "csca.mm"
include "mplring.mm"
include "mpllmod.mm"
include "asclf.mm"
include "syl2anc.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "ffvelrnd.mm"
include "impbida.mm"

theorem subrgasclcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  let vx: setvar x
  let cC: class C
  let vf: setvar f
  let vy: setvar y
  assume subrgascl.p: |- P = ( I mPoly R )
  assume subrgascl.a: |- A = ( algSc ` P )
  assume subrgascl.h: |- H = ( R |`s T )
  assume subrgascl.u: |- U = ( I mPoly H )
  assume subrgascl.i: |- ( ph -> I e. W )
  assume subrgascl.r: |- ( ph -> T e. ( SubRing ` R ) )
  assume subrgasclcl.b: |- B = ( Base ` U )
  assume subrgasclcl.k: |- K = ( Base ` R )
  assume subrgasclcl.x: |- ( ph -> X e. K )


  assert |- ( ph -> ( ( A ` X ) e. B <-> X e. T ) )

  proof
    wph
    cX
    cA
    cfv
    #
    cB
    wcel
    #
    cX
    cT
    wcel
    #
    wph
    @1
    wa
    #
    cX
    cH
    cbs
    cfv
    #
    cT
    @3
    cI
    cc0
    csn
    cxp
    #
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
    wcel
    #
    vx
    cv
    @5
    wceq
    #
    cX
    cR
    c0g
    cfv
    #
    cif
    #
    @4
    wcel
    #
    vx
    @6
    wral
    #
    cX
    @4
    wcel
    #
    @3
    cI
    cW
    wcel
    #
    @7
    wph
    @14
    @1
    subrgascl.i
    adantr
    @6
    vf
    cI
    cW
    @6
    eqid
    #
    psrbag0
    syl
    @3
    @6
    @4
    vx
    @6
    @10
    cmpt
    #
    wf
    @12
    @3
    cI
    cH
    cmps
    co
    #
    cbs
    cfv
    #
    @6
    cH
    @17
    vf
    cI
    @4
    @16
    @17
    eqid
    #
    @4
    eqid
    @15
    @18
    eqid
    #
    @3
    @0
    @16
    @18
    wph
    @0
    @16
    wceq
    @1
    wph
    vx
    cA
    cK
    @6
    cP
    cR
    vf
    cI
    cW
    cX
    @9
    subrgascl.p
    @15
    @9
    eqid
    subrgasclcl.k
    subrgascl.a
    subrgascl.i
    wph
    cT
    cR
    csubrg
    cfv
    wcel
    #
    cR
    crg
    wcel
    subrgascl.r
    cT
    cR
    subrgrcl
    syl
    subrgasclcl.x
    mplascl
    adantr
    wph
    cB
    @18
    @0
    wph
    cB
    @17
    csubrg
    cfv
    wcel
    cB
    @18
    wss
    wph
    cU
    cH
    @17
    cB
    cI
    cW
    @19
    subrgascl.u
    subrgasclcl.b
    subrgascl.i
    wph
    @21
    cH
    crg
    wcel
    #
    subrgascl.r
    cT
    cR
    cH
    subrgascl.h
    subrgring
    syl
    #
    mplsubrg
    cB
    @18
    @17
    @20
    subrgss
    syl
    sselda
    eqeltrrd
    psrelbas
    vx
    @6
    @4
    @10
    @16
    @16
    eqid
    fmpt
    sylibr
    @11
    @13
    vx
    @5
    @6
    @8
    @10
    cX
    @4
    @8
    cX
    @9
    iftrue
    eleq1d
    rspcv
    sylc
    wph
    cT
    @4
    wceq
    #
    @1
    wph
    @21
    @24
    subrgascl.r
    cT
    cR
    cH
    subrgascl.h
    subrgbas
    syl
    #
    adantr
    eleqtrrd
    wph
    @2
    wa
    #
    cX
    cU
    cascl
    cfv
    #
    cfv
    #
    @0
    cB
    wph
    @2
    @28
    cX
    cA
    cT
    cres
    #
    cfv
    @0
    wph
    cX
    @27
    @29
    wph
    cA
    @27
    cP
    cR
    cT
    cU
    cH
    cI
    cW
    subrgascl.p
    subrgascl.a
    subrgascl.h
    subrgascl.u
    subrgascl.i
    subrgascl.r
    @27
    eqid
    #
    subrgascl
    fveq1d
    cX
    cT
    cA
    fvres
    sylan9eq
    @26
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    cB
    cX
    @27
    wph
    @32
    cB
    @27
    wf
    #
    @2
    wph
    @14
    @22
    @33
    subrgascl.i
    @23
    @14
    @22
    wa
    @27
    cB
    @31
    @32
    cU
    @30
    @31
    eqid
    cU
    cH
    cI
    cW
    subrgascl.u
    mplring
    cU
    cH
    cI
    cW
    subrgascl.u
    mpllmod
    @32
    eqid
    subrgasclcl.b
    asclf
    syl2anc
    adantr
    wph
    @2
    cX
    @32
    wcel
    wph
    cT
    @32
    cX
    wph
    cT
    @4
    @32
    @25
    wph
    cH
    @31
    cbs
    wph
    cU
    cH
    cI
    cW
    crg
    subrgascl.u
    subrgascl.i
    @23
    mplsca
    fveq2d
    eqtrd
    eleq2d
    biimpa
    ffvelrnd
    eqeltrrd
    impbida
end
