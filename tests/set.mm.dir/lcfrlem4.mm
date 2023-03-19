include "cv.mm"
include "cfv.mm"
include "ciun.mm"
include "wss.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "clfn.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "cbs.mm"
include "lssel.mm"
include "sylan.mm"
include "wceq.mm"
include "ldualvbase.mm"
include "eleqtrd.mm"
include "lkrssv.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl6eleq.mm"
include "sseldd.mm"

theorem lcfrlem4
  let wph: wff ph
  let cD: class D
  let cQ: class Q
  let cU: class U
  let vg: setvar g
  let cE: class E
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  assume lcfrlem4.h: |- H = ( LHyp ` K )
  assume lcfrlem4.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfrlem4.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfrlem4.v: |- V = ( Base ` U )
  assume lcfrlem4.l: |- L = ( LKer ` U )
  assume lcfrlem4.d: |- D = ( LDual ` U )
  assume lcfrlem4.q: |- Q = ( LSubSp ` D )
  assume lcfrlem4.e: |- E = U_ g e. G ( ._|_ ` ( L ` g ) )
  assume lcfrlem4.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfrlem4.g: |- ( ph -> G e. Q )
  assume lcfrlem4.x: |- ( ph -> X e. E )

  disjoint V g
  disjoint g ph
  assert |- ( ph -> X e. V )

  proof
    wph
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
    cV
    cX
    wph
    @2
    cV
    wss
    #
    vg
    cG
    wral
    @3
    cV
    wss
    wph
    @4
    vg
    cG
    wph
    @0
    cG
    wcel
    #
    wa
    #
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @1
    cV
    wss
    @4
    wph
    @7
    @5
    lcfrlem4.k
    adantr
    @6
    cU
    clfn
    cfv
    #
    @0
    cL
    cV
    cU
    lcfrlem4.v
    @8
    eqid
    #
    lcfrlem4.l
    wph
    cU
    clmod
    wcel
    @5
    wph
    cU
    cH
    cK
    cW
    lcfrlem4.h
    lcfrlem4.u
    lcfrlem4.k
    dvhlmod
    #
    adantr
    @6
    @0
    cD
    cbs
    cfv
    #
    @8
    wph
    cG
    cQ
    wcel
    @5
    @0
    @11
    wcel
    lcfrlem4.g
    cQ
    cG
    @11
    cD
    @0
    @11
    eqid
    #
    lcfrlem4.q
    lssel
    sylan
    wph
    @11
    @8
    wceq
    @5
    wph
    cD
    @8
    @11
    cU
    clmod
    @9
    lcfrlem4.d
    @12
    @10
    ldualvbase
    adantr
    eleqtrd
    lkrssv
    cU
    cH
    cK
    c.pe
    cV
    cW
    @1
    lcfrlem4.h
    lcfrlem4.u
    lcfrlem4.v
    lcfrlem4.o
    dochssv
    syl2anc
    ralrimiva
    vg
    cG
    @2
    cV
    iunss
    sylibr
    wph
    cX
    cE
    @3
    lcfrlem4.x
    lcfrlem4.e
    syl6eleq
    sseldd
end
