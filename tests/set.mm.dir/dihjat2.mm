include "cv.mm"
include "csn.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "cbs.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "chlt.mm"
include "adantr.mm"
include "crn.mm"
include "simpr.mm"
include "dihjat1.mm"
include "oveq2.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "clmod.mm"
include "wrex.mm"
include "dvhlmod.mm"
include "islsati.mm"
include "syl2anc.mm"
include "r19.29a.mm"

theorem dihjat2
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cW: class W
  let cX: class X
  let vv: setvar v
  assume dihjat2.h: |- H = ( LHyp ` K )
  assume dihjat2.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihjat2.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume dihjat2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjat2.p: |- .(+) = ( LSSum ` U )
  assume dihjat2.a: |- A = ( LSAtoms ` U )
  assume dihjat2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dihjat2.x: |- ( ph -> X e. ran I )
  assume dihjat2.q: |- ( ph -> Q e. A )


  assert |- ( ph -> ( X .\/ Q ) = ( X .(+) Q ) )

  proof
    wph
    cQ
    vv
    cv
    #
    csn
    cU
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    cX
    cQ
    c.or
    co
    #
    cX
    cQ
    c.po
    co
    #
    wceq
    vv
    cU
    cbs
    cfv
    #
    wph
    @0
    @6
    wcel
    #
    wa
    #
    @3
    wa
    cX
    @2
    c.or
    co
    #
    cX
    @2
    c.po
    co
    #
    @4
    @5
    @8
    @9
    @10
    wceq
    @3
    @8
    c.po
    @0
    cU
    cH
    cI
    c.or
    cK
    @1
    @6
    cW
    cX
    dihjat2.h
    dihjat2.u
    @6
    eqid
    #
    dihjat2.p
    @1
    eqid
    #
    dihjat2.i
    dihjat2.j
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @7
    dihjat2.k
    adantr
    wph
    cX
    cI
    crn
    wcel
    @7
    dihjat2.x
    adantr
    wph
    @7
    simpr
    dihjat1
    adantr
    @3
    @4
    @9
    wceq
    @8
    cQ
    @2
    cX
    c.or
    oveq2
    adantl
    @3
    @5
    @10
    wceq
    @8
    cQ
    @2
    cX
    c.po
    oveq2
    adantl
    3eqtr4d
    wph
    cU
    clmod
    wcel
    cQ
    cA
    wcel
    @3
    vv
    @6
    wrex
    wph
    cU
    cH
    cK
    cW
    dihjat2.h
    dihjat2.u
    dihjat2.k
    dvhlmod
    dihjat2.q
    vv
    cA
    cQ
    @1
    @6
    cU
    clmod
    @11
    @12
    dihjat2.a
    islsati
    syl2anc
    r19.29a
end
