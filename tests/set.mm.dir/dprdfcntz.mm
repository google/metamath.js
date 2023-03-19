include "crn.mm"
include "cfv.mm"
include "wf.mm"
include "wss.mm"
include "wfn.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cbs.mm"
include "eqid.mm"
include "dprdff.mm"
include "ffn.mm"
include "syl.mm"
include "wa.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "ffvelrnda.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "wne.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simplr.mm"
include "dprdcntz.mm"
include "dprdfcl.mm"
include "ad2antrr.mm"
include "sseldd.mm"
include "adantlr.mm"
include "adantr.mm"
include "cntzi.mm"
include "syl2anc.mm"
include "pm2.61dane.mm"
include "ralrimiva.mm"
include "wb.mm"
include "oveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "ralrn.mm"
include "mpbird.mm"
include "frn.mm"
include "elcntz.mm"
include "mpbir2and.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem dprdfcntz
  let wph: wff ph
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vx: setvar x
  let cX: class X
  assume dprdff.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume dprdff.1: |- ( ph -> G dom DProd S )
  assume dprdff.2: |- ( ph -> dom S = I )
  assume dprdff.3: |- ( ph -> F e. W )
  assume dprdfcntz.z: |- Z = ( Cntz ` G )

  disjoint F h
  disjoint h i
  disjoint I h
  disjoint I i
  disjoint .0. h
  disjoint S h
  disjoint S i
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint h x
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X x
  disjoint Z y
  assert |- ( ph -> ran F C_ ( Z ` ran F ) )

  proof
    wph
    cI
    cF
    crn
    #
    cZ
    cfv
    #
    cF
    wf
    #
    @0
    @1
    wss
    wph
    cF
    cI
    wfn
    #
    vy
    cv
    #
    cF
    cfv
    #
    @1
    wcel
    #
    vy
    cI
    wral
    @2
    wph
    cI
    cG
    cbs
    cfv
    #
    cF
    wf
    #
    @3
    wph
    @7
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    c.0
    dprdff.w
    dprdff.1
    dprdff.2
    dprdff.3
    @7
    eqid
    #
    dprdff
    #
    cI
    @7
    cF
    ffn
    syl
    #
    wph
    @6
    vy
    cI
    wph
    @4
    cI
    wcel
    #
    wa
    #
    @6
    @5
    @7
    wcel
    #
    @5
    vx
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @15
    @5
    @16
    co
    #
    wceq
    #
    vx
    @0
    wral
    #
    wph
    cI
    @7
    @4
    cF
    @10
    ffvelrnda
    @13
    @20
    @5
    vz
    cv
    #
    cF
    cfv
    #
    @16
    co
    #
    @22
    @5
    @16
    co
    #
    wceq
    #
    vz
    cI
    wral
    #
    @13
    @25
    vz
    cI
    @13
    @21
    cI
    wcel
    #
    wa
    #
    @25
    @4
    @21
    @28
    @4
    @21
    wceq
    #
    wa
    #
    @5
    @22
    @22
    @5
    @16
    @30
    @4
    @21
    cF
    @28
    @29
    simpr
    #
    fveq2d
    @30
    @21
    @4
    cF
    @30
    @4
    @21
    @31
    eqcomd
    fveq2d
    oveq12d
    @28
    @4
    @21
    wne
    #
    wa
    #
    @5
    @21
    cS
    cfv
    #
    cZ
    cfv
    #
    wcel
    @22
    @34
    wcel
    #
    @25
    @33
    @4
    cS
    cfv
    #
    @35
    @5
    @33
    cS
    cG
    cI
    @4
    @21
    cZ
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    @12
    @27
    @32
    dprdff.1
    ad3antrrr
    wph
    cS
    cdm
    cI
    wceq
    @12
    @27
    @32
    dprdff.2
    ad3antrrr
    wph
    @12
    @27
    @32
    simpllr
    @13
    @27
    @32
    simplr
    @28
    @32
    simpr
    dprdfcntz.z
    dprdcntz
    @13
    @5
    @37
    wcel
    @27
    @32
    wph
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    @4
    c.0
    dprdff.w
    dprdff.1
    dprdff.2
    dprdff.3
    dprdfcl
    ad2antrr
    sseldd
    @28
    @36
    @32
    wph
    @27
    @36
    @12
    wph
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    @21
    c.0
    dprdff.w
    dprdff.1
    dprdff.2
    dprdff.3
    dprdfcl
    adantlr
    adantr
    @16
    @34
    cG
    @5
    @22
    cZ
    @16
    eqid
    #
    dprdfcntz.z
    cntzi
    syl2anc
    pm2.61dane
    ralrimiva
    @13
    @3
    @20
    @26
    wb
    wph
    @3
    @12
    @11
    adantr
    @19
    @25
    vx
    vz
    cI
    cF
    @15
    @22
    wceq
    @17
    @23
    @18
    @24
    @15
    @22
    @5
    @16
    oveq2
    @15
    @22
    @5
    @16
    oveq1
    eqeq12d
    ralrn
    syl
    mpbird
    @13
    @0
    @7
    wss
    #
    @6
    @14
    @20
    wa
    wb
    wph
    @39
    @12
    wph
    @8
    @39
    @10
    cI
    @7
    cF
    frn
    syl
    adantr
    vx
    @5
    @7
    @16
    @0
    cG
    cZ
    @9
    @38
    dprdfcntz.z
    elcntz
    syl
    mpbir2and
    ralrimiva
    vy
    cI
    @1
    cF
    ffnfv
    sylanbrc
    cI
    @1
    cF
    frn
    syl
end
