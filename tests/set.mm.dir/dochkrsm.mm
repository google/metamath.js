include "cfv.mm"
include "clsa.mm"
include "wcel.mm"
include "co.mm"
include "crn.mm"
include "c0g.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "chlt.mm"
include "adantr.mm"
include "simpr.mm"
include "dihsmatrn.mm"
include "oveq2.mm"
include "csubg.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "dihrnlss.mm"
include "syl2anc.mm"
include "lsssubg.mm"
include "lsm01.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "eqeltrd.mm"
include "dochsat0.mm"
include "mpjaodan.mm"

theorem dochkrsm
  let wph: wff ph
  let c.po: class .(+)
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  assume dochkrsm.h: |- H = ( LHyp ` K )
  assume dochkrsm.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochkrsm.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume dochkrsm.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochkrsm.p: |- .(+) = ( LSSum ` U )
  assume dochkrsm.f: |- F = ( LFnl ` U )
  assume dochkrsm.l: |- L = ( LKer ` U )
  assume dochkrsm.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dochkrsm.x: |- ( ph -> X e. ran I )
  assume dochkrsm.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( X .(+) ( ._|_ ` ( L ` G ) ) ) e. ran I )

  proof
    wph
    cG
    cL
    cfv
    c.pe
    cfv
    #
    cU
    clsa
    cfv
    #
    wcel
    #
    cX
    @0
    c.po
    co
    #
    cI
    crn
    #
    wcel
    @0
    cU
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    wph
    @2
    wa
    @1
    c.po
    @0
    cU
    cH
    cI
    cK
    cW
    cX
    dochkrsm.h
    dochkrsm.i
    dochkrsm.u
    dochkrsm.p
    @1
    eqid
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @2
    dochkrsm.k
    adantr
    wph
    cX
    @4
    wcel
    #
    @2
    dochkrsm.x
    adantr
    wph
    @2
    simpr
    dihsmatrn
    wph
    @7
    wa
    @3
    cX
    @4
    @7
    wph
    @3
    cX
    @6
    c.po
    co
    #
    cX
    @0
    @6
    cX
    c.po
    oveq2
    wph
    cX
    cU
    csubg
    cfv
    wcel
    #
    @11
    cX
    wceq
    wph
    cU
    clmod
    wcel
    cX
    cU
    clss
    cfv
    #
    wcel
    #
    @12
    wph
    cU
    cH
    cK
    cW
    dochkrsm.h
    dochkrsm.u
    dochkrsm.k
    dvhlmod
    wph
    @9
    @10
    @14
    dochkrsm.k
    dochkrsm.x
    @13
    cU
    cH
    cI
    cK
    cW
    cX
    dochkrsm.h
    dochkrsm.u
    dochkrsm.i
    @13
    eqid
    #
    dihrnlss
    syl2anc
    @13
    cX
    cU
    @15
    lsssubg
    syl2anc
    c.po
    cU
    cX
    @5
    @5
    eqid
    #
    dochkrsm.p
    lsm01
    syl
    sylan9eqr
    wph
    @10
    @7
    dochkrsm.x
    adantr
    eqeltrd
    wph
    @1
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    cW
    @5
    dochkrsm.h
    dochkrsm.o
    dochkrsm.u
    @16
    @8
    dochkrsm.f
    dochkrsm.l
    dochkrsm.k
    dochkrsm.g
    dochsat0
    mpjaodan
end
