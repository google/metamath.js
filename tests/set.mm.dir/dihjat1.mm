include "csn.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "c0g.mm"
include "wa.mm"
include "sneq.mm"
include "fveq2d.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lspsn0.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "oveq2d.mm"
include "djh01.mm"
include "adantr.mm"
include "csubg.mm"
include "clss.mm"
include "chlt.mm"
include "crn.mm"
include "dihrnlss.mm"
include "syl2anc.mm"
include "lsssubg.mm"
include "lsm01.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"
include "wne.mm"
include "cdif.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "dihjat1lem.mm"
include "pm2.61dane.mm"

theorem dihjat1
  let wph: wff ph
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vy: setvar y
  let vx: setvar x
  let vz: setvar z
  let c.0: class .0.
  assume dihjat1.h: |- H = ( LHyp ` K )
  assume dihjat1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjat1.v: |- V = ( Base ` U )
  assume dihjat1.p: |- .(+) = ( LSSum ` U )
  assume dihjat1.n: |- N = ( LSpan ` U )
  assume dihjat1.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjat1.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume dihjat1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjat1.x: |- ( ph -> X e. ran I )
  assume dihjat1.q: |- ( ph -> T e. V )


  assert |- ( ph -> ( X .\/ ( N ` { T } ) ) = ( X .(+) ( N ` { T } ) ) )

  proof
    wph
    cX
    cT
    csn
    #
    cN
    cfv
    #
    c.or
    co
    #
    cX
    @1
    c.po
    co
    #
    wceq
    cT
    cU
    c0g
    cfv
    #
    wph
    cT
    @4
    wceq
    #
    wa
    #
    @2
    cX
    @4
    csn
    #
    c.or
    co
    #
    cX
    @3
    @6
    @1
    @7
    cX
    c.or
    @5
    wph
    @1
    @7
    cN
    cfv
    #
    @7
    @5
    @0
    @7
    cN
    cT
    @4
    sneq
    fveq2d
    wph
    cU
    clmod
    wcel
    #
    @9
    @7
    wceq
    wph
    cU
    cH
    cK
    cW
    dihjat1.h
    dihjat1.u
    dihjat1.k
    dvhlmod
    #
    cN
    cU
    @4
    @4
    eqid
    #
    dihjat1.n
    lspsn0
    syl
    sylan9eqr
    #
    oveq2d
    wph
    @8
    cX
    wceq
    @5
    wph
    cU
    cH
    cI
    c.or
    cK
    cW
    cX
    @4
    dihjat1.h
    dihjat1.u
    @12
    dihjat1.i
    dihjat1.j
    dihjat1.k
    dihjat1.x
    djh01
    adantr
    @6
    @3
    cX
    @7
    c.po
    co
    #
    cX
    @6
    @1
    @7
    cX
    c.po
    @13
    oveq2d
    wph
    @14
    cX
    wceq
    #
    @5
    wph
    cX
    cU
    csubg
    cfv
    wcel
    #
    @15
    wph
    @10
    cX
    cU
    clss
    cfv
    #
    wcel
    #
    @16
    @11
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cI
    crn
    wcel
    #
    @18
    dihjat1.k
    dihjat1.x
    @17
    cU
    cH
    cI
    cK
    cW
    cX
    dihjat1.h
    dihjat1.u
    dihjat1.i
    @17
    eqid
    #
    dihrnlss
    syl2anc
    @17
    cX
    cU
    @21
    lsssubg
    syl2anc
    c.po
    cU
    cX
    @4
    @12
    dihjat1.p
    lsm01
    syl
    adantr
    eqtr2d
    3eqtrd
    wph
    cT
    @4
    wne
    #
    wa
    #
    c.po
    cT
    cU
    cH
    cI
    c.or
    cK
    cN
    cV
    cW
    cX
    @4
    dihjat1.h
    dihjat1.u
    dihjat1.v
    dihjat1.p
    dihjat1.n
    dihjat1.i
    dihjat1.j
    wph
    @19
    @22
    dihjat1.k
    adantr
    wph
    @20
    @22
    dihjat1.x
    adantr
    @12
    @23
    cT
    cV
    wcel
    #
    @22
    wa
    cT
    cV
    @7
    cdif
    wcel
    wph
    @24
    @22
    dihjat1.q
    anim1i
    cT
    cV
    @4
    eldifsn
    sylibr
    dihjat1lem
    pm2.61dane
end
