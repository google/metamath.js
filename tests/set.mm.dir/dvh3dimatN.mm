include "cv.mm"
include "co.mm"
include "wss.mm"
include "wn.mm"
include "wrex.mm"
include "dvh4dimat.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "clmod.mm"
include "clss.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lsatlssel.mm"
include "lsssubg.mm"
include "syl2anc.mm"
include "lsmidm.mm"
include "syl.mm"
include "oveq1d.mm"
include "sseq2d.mm"
include "notbid.mm"
include "rexbidv.mm"
include "mpbid.mm"

theorem dvh3dimatN
  let wph: wff ph
  let cA: class A
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let vs: setvar s
  let vr: setvar r
  let cR: class R
  assume dvh4dimat.h: |- H = ( LHyp ` K )
  assume dvh4dimat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh3dimat.s: |- .(+) = ( LSSum ` U )
  assume dvh3dimat.a: |- A = ( LSAtoms ` U )
  assume dvh3dimat.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dvh3dimat.p: |- ( ph -> P e. A )
  assume dvh3dimat.q: |- ( ph -> Q e. A )

  disjoint A s
  disjoint K s
  disjoint P s
  disjoint Q s
  disjoint .(+) s
  disjoint W s
  disjoint ph s
  disjoint r s
  disjoint A r
  disjoint K r
  disjoint P r
  disjoint Q r
  disjoint R r
  disjoint R s
  disjoint .(+) r
  disjoint W r
  disjoint ph r
  assert |- ( ph -> E. s e. A -. s C_ ( P .(+) Q ) )

  proof
    wph
    vs
    cv
    #
    cP
    cP
    c.po
    co
    #
    cQ
    c.po
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
    cQ
    c.po
    co
    #
    wss
    #
    wn
    #
    vs
    cA
    wrex
    wph
    cA
    cP
    c.po
    cP
    cQ
    cU
    cH
    cK
    cW
    vs
    dvh4dimat.h
    dvh4dimat.u
    dvh3dimat.s
    dvh3dimat.a
    dvh3dimat.k
    dvh3dimat.p
    dvh3dimat.p
    dvh3dimat.q
    dvh4dimat
    wph
    @4
    @7
    vs
    cA
    wph
    @3
    @6
    wph
    @2
    @5
    @0
    wph
    @1
    cP
    cQ
    c.po
    wph
    cP
    cU
    csubg
    cfv
    wcel
    #
    @1
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
    @8
    wph
    cU
    cH
    cK
    cW
    dvh4dimat.h
    dvh4dimat.u
    dvh3dimat.k
    dvhlmod
    #
    wph
    cA
    @9
    cP
    cU
    @9
    eqid
    #
    dvh3dimat.a
    @10
    dvh3dimat.p
    lsatlssel
    @9
    cP
    cU
    @11
    lsssubg
    syl2anc
    c.po
    cP
    cU
    dvh3dimat.s
    lsmidm
    syl
    oveq1d
    sseq2d
    notbid
    rexbidv
    mpbid
end
