include "cv.mm"
include "clsm.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "wn.mm"
include "wrex.mm"
include "wne.mm"
include "eqid.mm"
include "dvh3dimatN.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "csubg.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "lsatlssel.mm"
include "lsssubg.mm"
include "syl2anc.mm"
include "lsmidm.mm"
include "syl.mm"
include "sseq2d.mm"
include "adantr.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "simpr.mm"
include "lsatcmp.mm"
include "bitrd.mm"
include "necon3bbid.mm"
include "rexbidva.mm"
include "mpbid.mm"

theorem dvh2dimatN
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let vs: setvar s
  let vr: setvar r
  let cQ: class Q
  let cR: class R
  let c.po: class .(+)
  assume dvh4dimat.h: |- H = ( LHyp ` K )
  assume dvh4dimat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh2dimat.a: |- A = ( LSAtoms ` U )
  assume dvh2dimat.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dvh2dimat.p: |- ( ph -> P e. A )

  disjoint U s
  disjoint A s
  disjoint K s
  disjoint P s
  disjoint W s
  disjoint ph s
  disjoint r s
  disjoint A r
  disjoint K r
  disjoint P r
  disjoint Q r
  disjoint Q s
  disjoint R r
  disjoint R s
  disjoint .(+) r
  disjoint .(+) s
  disjoint W r
  disjoint ph r
  assert |- ( ph -> E. s e. A s =/= P )

  proof
    wph
    vs
    cv
    #
    cP
    cP
    cU
    clsm
    cfv
    #
    co
    #
    wss
    #
    wn
    #
    vs
    cA
    wrex
    @0
    cP
    wne
    #
    vs
    cA
    wrex
    wph
    cA
    cP
    @1
    cP
    cU
    cH
    cK
    cW
    vs
    dvh4dimat.h
    dvh4dimat.u
    @1
    eqid
    #
    dvh2dimat.a
    dvh2dimat.k
    dvh2dimat.p
    dvh2dimat.p
    dvh3dimatN
    wph
    @4
    @5
    vs
    cA
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @3
    @0
    cP
    @8
    @3
    @0
    cP
    wss
    #
    @0
    cP
    wceq
    wph
    @3
    @9
    wb
    @7
    wph
    @2
    cP
    @0
    wph
    cP
    cU
    csubg
    cfv
    wcel
    #
    @2
    cP
    wceq
    wph
    cU
    clmod
    wcel
    cP
    cU
    clss
    cfv
    #
    wcel
    @10
    wph
    cU
    cH
    cK
    cW
    dvh4dimat.h
    dvh4dimat.u
    dvh2dimat.k
    dvhlmod
    #
    wph
    cA
    @11
    cP
    cU
    @11
    eqid
    #
    dvh2dimat.a
    @12
    dvh2dimat.p
    lsatlssel
    @11
    cP
    cU
    @13
    lsssubg
    syl2anc
    @1
    cP
    cU
    @6
    lsmidm
    syl
    sseq2d
    adantr
    @8
    cA
    @0
    cP
    cU
    dvh2dimat.a
    wph
    cU
    clvec
    wcel
    @7
    wph
    cU
    cH
    cK
    cW
    dvh4dimat.h
    dvh4dimat.u
    dvh2dimat.k
    dvhlvec
    adantr
    wph
    @7
    simpr
    wph
    cP
    cA
    wcel
    @7
    dvh2dimat.p
    adantr
    lsatcmp
    bitrd
    necon3bbid
    rexbidva
    mpbid
end
