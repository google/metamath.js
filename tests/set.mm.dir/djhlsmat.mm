include "csn.mm"
include "cfv.mm"
include "co.mm"
include "crn.mm"
include "wcel.mm"
include "wceq.mm"
include "cpr.mm"
include "cun.mm"
include "clmod.mm"
include "wss.mm"
include "dvhlmod.mm"
include "snssd.mm"
include "lsmsp2.mm"
include "syl3anc.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "dihprrn.mm"
include "eqeltrd.mm"
include "clss.mm"
include "eqid.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "djhlsmcl.mm"
include "mpbid.mm"

theorem djhlsmat
  let wph: wff ph
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume djhlsmat.h: |- H = ( LHyp ` K )
  assume djhlsmat.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhlsmat.v: |- V = ( Base ` U )
  assume djhlsmat.p: |- .(+) = ( LSSum ` U )
  assume djhlsmat.n: |- N = ( LSpan ` U )
  assume djhlsmat.i: |- I = ( ( DIsoH ` K ) ` W )
  assume djhlsmat.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume djhlsmat.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume djhlsmat.x: |- ( ph -> X e. V )
  assume djhlsmat.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( ( N ` { X } ) .(+) ( N ` { Y } ) ) = ( ( N ` { X } ) .\/ ( N ` { Y } ) ) )

  proof
    wph
    cX
    csn
    #
    cN
    cfv
    #
    cY
    csn
    #
    cN
    cfv
    #
    c.po
    co
    #
    cI
    crn
    #
    wcel
    @4
    @1
    @3
    c.or
    co
    wceq
    wph
    @4
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    @5
    wph
    @4
    @0
    @2
    cun
    #
    cN
    cfv
    #
    @7
    wph
    cU
    clmod
    wcel
    #
    @0
    cV
    wss
    @2
    cV
    wss
    @4
    @9
    wceq
    wph
    cU
    cH
    cK
    cW
    djhlsmat.h
    djhlsmat.u
    djhlsmat.k
    dvhlmod
    #
    wph
    cX
    cV
    djhlsmat.x
    snssd
    wph
    cY
    cV
    djhlsmat.y
    snssd
    c.po
    @0
    @2
    cN
    cV
    cU
    djhlsmat.v
    djhlsmat.n
    djhlsmat.p
    lsmsp2
    syl3anc
    @6
    @8
    cN
    cX
    cY
    df-pr
    fveq2i
    syl6eqr
    wph
    cU
    cH
    cI
    cK
    cN
    cV
    cW
    cX
    cY
    djhlsmat.h
    djhlsmat.u
    djhlsmat.v
    djhlsmat.n
    djhlsmat.i
    djhlsmat.k
    djhlsmat.x
    djhlsmat.y
    dihprrn
    eqeltrd
    wph
    c.po
    cU
    clss
    cfv
    #
    cU
    cH
    cI
    c.or
    cK
    cV
    cW
    @1
    @3
    djhlsmat.h
    djhlsmat.u
    djhlsmat.v
    @12
    eqid
    #
    djhlsmat.p
    djhlsmat.i
    djhlsmat.j
    djhlsmat.k
    wph
    @10
    cX
    cV
    wcel
    @1
    @12
    wcel
    @11
    djhlsmat.x
    @12
    cN
    cV
    cU
    cX
    djhlsmat.v
    @13
    djhlsmat.n
    lspsncl
    syl2anc
    wph
    @10
    cY
    cV
    wcel
    @3
    @12
    wcel
    @11
    djhlsmat.y
    @12
    cN
    cV
    cU
    cY
    djhlsmat.v
    @13
    djhlsmat.n
    lspsncl
    syl2anc
    djhlsmcl
    mpbid
end
