include "co.mm"
include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "wcel.mm"
include "wrex.mm"
include "syl6eleq.mm"
include "eliun.mm"
include "sylib.mm"
include "wa.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "adantr.mm"
include "chlt.mm"
include "cbs.mm"
include "wss.mm"
include "clfn.mm"
include "eqid.mm"
include "lssel.mm"
include "sylan.mm"
include "wceq.mm"
include "ldualvbase.mm"
include "eleqtrd.mm"
include "lkrssv.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "simpr.mm"
include "csn.mm"
include "eqsstr3d.mm"
include "ex.mm"
include "lcfrlem4.mm"
include "lspsnel5.mm"
include "3imtr4d.mm"
include "imp.mm"
include "lssvacl.mm"
include "syl22anc.mm"
include "reximdva.mm"
include "mpd.mm"
include "sylibr.mm"
include "syl6eleqr.mm"

theorem lcfrlem6
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cU: class U
  let vg: setvar g
  let cE: class E
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cN: class N
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lcfrlem6.h: |- H = ( LHyp ` K )
  assume lcfrlem6.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem6.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem6.p: |- .+ = ( +g ` U )
  assume lcfrlem6.n: |- N = ( LSpan ` U )
  assume lcfrlem6.l: |- L = ( LKer ` U )
  assume lcfrlem6.d: |- D = ( LDual ` U )
  assume lcfrlem6.q: |- Q = ( LSubSp ` D )
  assume lcfrlem6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem6.g: |- ( ph -> G e. Q )
  assume lcfrlem6.e: |- E = U_ g e. G ( ._|_ ` ( L ` g ) )
  assume lcfrlem6.x: |- ( ph -> X e. E )
  assume lcfrlem6.y: |- ( ph -> Y e. E )
  assume lcfrlem6.en: |- ( ph -> ( N ` { X } ) = ( N ` { Y } ) )

  disjoint .+ g
  disjoint U g
  disjoint X g
  disjoint Y g
  disjoint g ph
  assert |- ( ph -> ( X .+ Y ) e. E )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    vg
    cG
    vg
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
    cE
    wph
    @0
    @3
    wcel
    #
    vg
    cG
    wrex
    #
    @0
    @4
    wcel
    wph
    cX
    @3
    wcel
    #
    vg
    cG
    wrex
    #
    @6
    wph
    cX
    @4
    wcel
    @8
    wph
    cX
    cE
    @4
    lcfrlem6.x
    lcfrlem6.e
    syl6eleq
    vg
    cX
    cG
    @3
    eliun
    sylib
    wph
    @7
    @5
    vg
    cG
    wph
    @1
    cG
    wcel
    #
    wa
    #
    @7
    @5
    @10
    @7
    wa
    cU
    clmod
    wcel
    #
    @3
    cU
    clss
    cfv
    #
    wcel
    #
    @7
    cY
    @3
    wcel
    #
    @5
    @10
    @11
    @7
    wph
    @11
    @9
    wph
    cU
    cH
    cK
    cW
    lcfrlem6.h
    lcfrlem6.u
    lcfrlem6.k
    dvhlmod
    #
    adantr
    #
    adantr
    @10
    @13
    @7
    @10
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @2
    cU
    cbs
    cfv
    #
    wss
    @13
    wph
    @17
    @9
    lcfrlem6.k
    adantr
    @10
    cU
    clfn
    cfv
    #
    @1
    cL
    @18
    cU
    @18
    eqid
    #
    @19
    eqid
    #
    lcfrlem6.l
    @16
    @10
    @1
    cD
    cbs
    cfv
    #
    @19
    wph
    cG
    cQ
    wcel
    @9
    @1
    @22
    wcel
    lcfrlem6.g
    cQ
    cG
    @22
    cD
    @1
    @22
    eqid
    #
    lcfrlem6.q
    lssel
    sylan
    wph
    @22
    @19
    wceq
    @9
    wph
    cD
    @19
    @22
    cU
    clmod
    @21
    lcfrlem6.d
    @23
    @15
    ldualvbase
    adantr
    eleqtrd
    lkrssv
    @12
    cU
    cH
    cK
    c.pe
    @18
    cW
    @2
    lcfrlem6.h
    lcfrlem6.u
    @20
    @12
    eqid
    #
    lcfrlem6.o
    dochlss
    syl2anc
    #
    adantr
    @10
    @7
    simpr
    @10
    @7
    @14
    @10
    cX
    csn
    cN
    cfv
    #
    @3
    wss
    #
    cY
    csn
    cN
    cfv
    #
    @3
    wss
    #
    @7
    @14
    @10
    @27
    @29
    @10
    @27
    wa
    @28
    @26
    @3
    @10
    @26
    @28
    wceq
    #
    @27
    wph
    @30
    @9
    lcfrlem6.en
    adantr
    adantr
    @10
    @27
    simpr
    eqsstr3d
    ex
    @10
    @12
    @3
    cN
    @18
    cU
    cX
    @20
    @24
    lcfrlem6.n
    @16
    @25
    wph
    cX
    @18
    wcel
    @9
    wph
    cD
    cQ
    cU
    vg
    cE
    cG
    cH
    cK
    cL
    c.pe
    @18
    cW
    cX
    lcfrlem6.h
    lcfrlem6.o
    lcfrlem6.u
    @20
    lcfrlem6.l
    lcfrlem6.d
    lcfrlem6.q
    lcfrlem6.e
    lcfrlem6.k
    lcfrlem6.g
    lcfrlem6.x
    lcfrlem4
    adantr
    lspsnel5
    @10
    @12
    @3
    cN
    @18
    cU
    cY
    @20
    @24
    lcfrlem6.n
    @16
    @25
    wph
    cY
    @18
    wcel
    @9
    wph
    cD
    cQ
    cU
    vg
    cE
    cG
    cH
    cK
    cL
    c.pe
    @18
    cW
    cY
    lcfrlem6.h
    lcfrlem6.o
    lcfrlem6.u
    @20
    lcfrlem6.l
    lcfrlem6.d
    lcfrlem6.q
    lcfrlem6.e
    lcfrlem6.k
    lcfrlem6.g
    lcfrlem6.y
    lcfrlem4
    adantr
    lspsnel5
    3imtr4d
    imp
    c.pl
    @12
    @3
    cU
    cX
    cY
    lcfrlem6.p
    @24
    lssvacl
    syl22anc
    ex
    reximdva
    mpd
    vg
    @0
    cG
    @3
    eliun
    sylibr
    lcfrlem6.e
    syl6eleqr
end
