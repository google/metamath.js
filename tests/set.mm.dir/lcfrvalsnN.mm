include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "wcel.mm"
include "wrex.mm"
include "eliun.mm"
include "csn.mm"
include "wi.mm"
include "eleq2i.mm"
include "wa.mm"
include "chlt.mm"
include "cbs.mm"
include "wss.mm"
include "adantr.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "clss.mm"
include "lduallmod.mm"
include "ldualelvbase.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lssel.mm"
include "sylan.mm"
include "wceq.mm"
include "ldualvbase.mm"
include "eleqtrd.mm"
include "lkrssv.mm"
include "cvsca.mm"
include "co.mm"
include "csca.mm"
include "wb.mm"
include "lspsnel.mm"
include "ldualsbase.mm"
include "rexeqdv.mm"
include "bitrd.mm"
include "biimpa.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lkrss2N.mm"
include "mpbird.mm"
include "dochss.mm"
include "syl3anc.mm"
include "sseld.mm"
include "ex.mm"
include "syl5bi.mm"
include "rexlimdv.mm"
include "lspsnid.mm"
include "syl6eleqr.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "impbid.mm"
include "syl5bb.mm"
include "eqrdv.mm"
include "syl5eq.mm"

theorem lcfrvalsnN
  let wph: wff ph
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cN: class N
  let c.pe: class ._|_
  let cW: class W
  let vx: setvar x
  let vk: setvar k
  assume lcfrvalsn.h: |- H = ( LHyp ` K )
  assume lcfrvalsn.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrvalsn.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrvalsn.f: |- F = ( LFnl ` U )
  assume lcfrvalsn.l: |- L = ( LKer ` U )
  assume lcfrvalsn.d: |- D = ( LDual ` U )
  assume lcfrvalsn.n: |- N = ( LSpan ` D )
  assume lcfrvalsn.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrvalsn.g: |- ( ph -> G e. F )
  assume lcfrvalsn.q: |- Q = U_ f e. R ( ._|_ ` ( L ` f ) )
  assume lcfrvalsn.r: |- R = ( N ` { G } )

  disjoint ._|_ f
  disjoint G f
  disjoint R f
  disjoint L f
  disjoint f ph
  disjoint f x
  disjoint ._|_ x
  disjoint D k
  disjoint F k
  disjoint f k
  disjoint k x
  disjoint G k
  disjoint G x
  disjoint N k
  disjoint R x
  disjoint L k
  disjoint L x
  disjoint k ph
  disjoint ph x
  disjoint U k
  assert |- ( ph -> Q = ( ._|_ ` ( L ` G ) ) )

  proof
    wph
    cQ
    vf
    cR
    vf
    cv
    #
    cL
    cfv
    #
    c.pe
    cfv
    #
    ciun
    #
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    lcfrvalsn.q
    wph
    vx
    @3
    @5
    vx
    cv
    #
    @3
    wcel
    @6
    @2
    wcel
    #
    vf
    cR
    wrex
    #
    wph
    @6
    @5
    wcel
    #
    vf
    @6
    cR
    @2
    eliun
    wph
    @8
    @9
    wph
    @7
    @9
    vf
    cR
    @0
    cR
    wcel
    @0
    cG
    csn
    cN
    cfv
    #
    wcel
    #
    wph
    @7
    @9
    wi
    #
    cR
    @10
    @0
    lcfrvalsn.r
    eleq2i
    wph
    @11
    @12
    wph
    @11
    wa
    #
    @2
    @5
    @6
    @13
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    cU
    cbs
    cfv
    #
    wss
    @4
    @1
    wss
    #
    @2
    @5
    wss
    wph
    @14
    @11
    lcfrvalsn.k
    adantr
    @13
    cF
    @0
    cL
    @15
    cU
    @15
    eqid
    #
    lcfrvalsn.f
    lcfrvalsn.l
    wph
    cU
    clmod
    wcel
    @11
    wph
    cU
    cH
    cK
    cW
    lcfrvalsn.h
    lcfrvalsn.u
    lcfrvalsn.k
    dvhlmod
    #
    adantr
    @13
    @0
    cD
    cbs
    cfv
    #
    cF
    wph
    @10
    cD
    clss
    cfv
    #
    wcel
    #
    @11
    @0
    @19
    wcel
    wph
    cD
    clmod
    wcel
    #
    cG
    @19
    wcel
    #
    @21
    wph
    cD
    cU
    lcfrvalsn.d
    @18
    lduallmod
    #
    wph
    cD
    cF
    cG
    @19
    cU
    clmod
    lcfrvalsn.f
    lcfrvalsn.d
    @19
    eqid
    #
    @18
    lcfrvalsn.g
    ldualelvbase
    #
    @20
    cN
    @19
    cD
    cG
    @25
    @20
    eqid
    #
    lcfrvalsn.n
    lspsncl
    syl2anc
    @20
    @10
    @19
    cD
    @0
    @25
    @27
    lssel
    sylan
    wph
    @19
    cF
    wceq
    @11
    wph
    cD
    cF
    @19
    cU
    clmod
    lcfrvalsn.f
    lcfrvalsn.d
    @25
    @18
    ldualvbase
    adantr
    eleqtrd
    #
    lkrssv
    @13
    @16
    @0
    vk
    cv
    cG
    cD
    cvsca
    cfv
    #
    co
    wceq
    #
    vk
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    wph
    @11
    @33
    wph
    @11
    @30
    vk
    cD
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    @33
    wph
    @22
    @23
    @11
    @36
    wb
    @24
    @26
    @29
    @0
    vk
    @34
    @35
    cN
    @19
    cD
    cG
    @34
    eqid
    #
    @35
    eqid
    #
    @25
    @29
    eqid
    #
    lcfrvalsn.n
    lspsnel
    syl2anc
    wph
    @30
    vk
    @35
    @32
    wph
    cD
    @34
    @31
    @35
    @32
    clmod
    cU
    @31
    eqid
    #
    @32
    eqid
    #
    lcfrvalsn.d
    @37
    @38
    @18
    ldualsbase
    rexeqdv
    bitrd
    biimpa
    @13
    cD
    @32
    @31
    @29
    cF
    cG
    @0
    cL
    cU
    vk
    @40
    @41
    lcfrvalsn.f
    lcfrvalsn.l
    lcfrvalsn.d
    @39
    wph
    cU
    clvec
    wcel
    @11
    wph
    cU
    cH
    cK
    cW
    lcfrvalsn.h
    lcfrvalsn.u
    lcfrvalsn.k
    dvhlvec
    adantr
    wph
    cG
    cF
    wcel
    @11
    lcfrvalsn.g
    adantr
    @28
    lkrss2N
    mpbird
    cU
    cH
    cK
    c.pe
    @15
    cW
    @4
    @1
    lcfrvalsn.h
    lcfrvalsn.u
    @17
    lcfrvalsn.o
    dochss
    syl3anc
    sseld
    ex
    syl5bi
    rexlimdv
    wph
    @9
    @8
    wph
    cG
    cR
    wcel
    @9
    @8
    wph
    cG
    @10
    cR
    wph
    @22
    @23
    cG
    @10
    wcel
    @24
    @26
    cN
    @19
    cD
    cG
    @25
    lcfrvalsn.n
    lspsnid
    syl2anc
    lcfrvalsn.r
    syl6eleqr
    @7
    @9
    vf
    cG
    cR
    @0
    cG
    wceq
    #
    @2
    @5
    @6
    @42
    @1
    @4
    c.pe
    @0
    cG
    cL
    fveq2
    fveq2d
    eleq2d
    rspcev
    sylan
    ex
    impbid
    syl5bb
    eqrdv
    syl5eq
end
