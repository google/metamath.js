include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "cplusg.mm"
include "wceq.mm"
include "csubg.mm"
include "wb.mm"
include "clmod.mm"
include "lsssubg.mm"
include "syl2anc.mm"
include "eqid.mm"
include "lsmelval.mm"
include "wi.mm"
include "adantr.mm"
include "simprl.mm"
include "lssel.mm"
include "lspsncl.mm"
include "simprr.mm"
include "lspsnid.mm"
include "lsmelvali.mm"
include "syl22anc.mm"
include "eleq1a.mm"
include "syl.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "lspsnel6.mm"
include "sylibd.mm"
include "reximdvva.mm"
include "sylbid.mm"
include "lspsnel5a.mm"
include "lsmless1.mm"
include "lsmless2.mm"
include "sstrd.mm"
include "sseld.mm"
include "sylbird.mm"
include "rexlimdvva.mm"
include "impbid.mm"
include "r19.42v.mm"
include "rexbii.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem lsmelval2
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lsmelval2.v: |- V = ( Base ` W )
  assume lsmelval2.s: |- S = ( LSubSp ` W )
  assume lsmelval2.p: |- .(+) = ( LSSum ` W )
  assume lsmelval2.n: |- N = ( LSpan ` W )
  assume lsmelval2.w: |- ( ph -> W e. LMod )
  assume lsmelval2.t: |- ( ph -> T e. S )
  assume lsmelval2.u: |- ( ph -> U e. S )

  disjoint y z
  disjoint .(+) y
  disjoint .(+) z
  disjoint T y
  disjoint T z
  disjoint U y
  disjoint U z
  disjoint V y
  disjoint V z
  disjoint W y
  disjoint W z
  disjoint X y
  disjoint X z
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( X e. ( T .(+) U ) <-> ( X e. V /\ E. y e. T E. z e. U ( N ` { X } ) C_ ( ( N ` { y } ) .(+) ( N ` { z } ) ) ) ) )

  proof
    wph
    cX
    cT
    cU
    c.po
    co
    #
    wcel
    #
    cX
    cV
    wcel
    #
    cX
    csn
    cN
    cfv
    vy
    cv
    #
    csn
    cN
    cfv
    #
    vz
    cv
    #
    csn
    cN
    cfv
    #
    c.po
    co
    #
    wss
    #
    wa
    #
    vz
    cU
    wrex
    #
    vy
    cT
    wrex
    #
    @2
    @8
    vz
    cU
    wrex
    #
    vy
    cT
    wrex
    wa
    #
    wph
    @1
    @11
    wph
    @1
    cX
    @3
    @5
    cW
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vz
    cU
    wrex
    vy
    cT
    wrex
    #
    @11
    wph
    cT
    cW
    csubg
    cfv
    #
    wcel
    #
    cU
    @18
    wcel
    #
    @1
    @17
    wb
    wph
    cW
    clmod
    wcel
    #
    cT
    cS
    wcel
    #
    @19
    lsmelval2.w
    lsmelval2.t
    cS
    cT
    cW
    lsmelval2.s
    lsssubg
    syl2anc
    #
    wph
    @21
    cU
    cS
    wcel
    #
    @20
    lsmelval2.w
    lsmelval2.u
    cS
    cU
    cW
    lsmelval2.s
    lsssubg
    syl2anc
    #
    vy
    vz
    @14
    c.po
    cT
    cU
    cW
    cX
    @14
    eqid
    #
    lsmelval2.p
    lsmelval
    syl2anc
    wph
    @16
    @9
    vy
    vz
    cT
    cU
    wph
    @3
    cT
    wcel
    #
    @5
    cU
    wcel
    #
    wa
    #
    wa
    #
    @16
    cX
    @7
    wcel
    #
    @9
    @30
    @15
    @7
    wcel
    #
    @16
    @31
    wi
    @30
    @4
    @18
    wcel
    #
    @6
    @18
    wcel
    #
    @3
    @4
    wcel
    #
    @5
    @6
    wcel
    #
    @32
    @30
    @21
    @4
    cS
    wcel
    #
    @33
    wph
    @21
    @29
    lsmelval2.w
    adantr
    #
    @30
    @21
    @3
    cV
    wcel
    #
    @37
    @38
    @30
    @22
    @27
    @39
    wph
    @22
    @29
    lsmelval2.t
    adantr
    #
    wph
    @27
    @28
    simprl
    #
    cS
    cT
    cV
    cW
    @3
    lsmelval2.v
    lsmelval2.s
    lssel
    syl2anc
    #
    cS
    cN
    cV
    cW
    @3
    lsmelval2.v
    lsmelval2.s
    lsmelval2.n
    lspsncl
    syl2anc
    #
    cS
    @4
    cW
    lsmelval2.s
    lsssubg
    syl2anc
    @30
    @21
    @6
    cS
    wcel
    #
    @34
    @38
    @30
    @21
    @5
    cV
    wcel
    #
    @44
    @38
    @30
    @24
    @28
    @45
    wph
    @24
    @29
    lsmelval2.u
    adantr
    #
    wph
    @27
    @28
    simprr
    #
    cS
    cU
    cV
    cW
    @5
    lsmelval2.v
    lsmelval2.s
    lssel
    syl2anc
    #
    cS
    cN
    cV
    cW
    @5
    lsmelval2.v
    lsmelval2.s
    lsmelval2.n
    lspsncl
    syl2anc
    #
    cS
    @6
    cW
    lsmelval2.s
    lsssubg
    syl2anc
    #
    @30
    @21
    @39
    @35
    @38
    @42
    cN
    cV
    cW
    @3
    lsmelval2.v
    lsmelval2.n
    lspsnid
    syl2anc
    @30
    @21
    @45
    @36
    @38
    @48
    cN
    cV
    cW
    @5
    lsmelval2.v
    lsmelval2.n
    lspsnid
    syl2anc
    @14
    c.po
    @4
    @6
    cW
    @3
    @5
    @26
    lsmelval2.p
    lsmelvali
    syl22anc
    @15
    @7
    cX
    eleq1a
    syl
    @30
    cS
    @7
    cN
    cV
    cW
    cX
    lsmelval2.v
    lsmelval2.s
    lsmelval2.n
    @38
    @30
    @21
    @37
    @44
    @7
    cS
    wcel
    @38
    @43
    @49
    c.po
    cS
    @4
    @6
    cW
    lsmelval2.s
    lsmelval2.p
    lsmcl
    syl3anc
    lspsnel6
    #
    sylibd
    reximdvva
    sylbid
    wph
    @9
    @1
    vy
    vz
    cT
    cU
    @30
    @9
    @31
    @1
    @51
    @30
    @7
    @0
    cX
    @30
    @7
    cT
    @6
    c.po
    co
    #
    @0
    @30
    @19
    @34
    @4
    cT
    wss
    @7
    @52
    wss
    wph
    @19
    @29
    @23
    adantr
    #
    @50
    @30
    cS
    cT
    cN
    cW
    @3
    lsmelval2.s
    lsmelval2.n
    @38
    @40
    @41
    lspsnel5a
    c.po
    @4
    cT
    @6
    cW
    lsmelval2.p
    lsmless1
    syl3anc
    @30
    @19
    @20
    @6
    cU
    wss
    @52
    @0
    wss
    @53
    wph
    @20
    @29
    @25
    adantr
    @30
    cS
    cU
    cN
    cW
    @5
    lsmelval2.s
    lsmelval2.n
    @38
    @46
    @47
    lspsnel5a
    c.po
    cT
    @6
    cU
    cW
    lsmelval2.p
    lsmless2
    syl3anc
    sstrd
    sseld
    sylbird
    rexlimdvva
    impbid
    @11
    @2
    @12
    wa
    #
    vy
    cT
    wrex
    @13
    @10
    @54
    vy
    cT
    @2
    @8
    vz
    cU
    r19.42v
    rexbii
    @2
    @12
    vy
    cT
    r19.42v
    bitri
    syl6bb
end
