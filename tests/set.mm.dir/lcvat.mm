include "cv.mm"
include "co.mm"
include "wpss.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wceq.mm"
include "clmod.mm"
include "lcvpss.mm"
include "lrelat.mm"
include "wcel.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "lsatlssel.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "wbr.mm"
include "simp3l.mm"
include "simp3r.mm"
include "lcvnbtwn2.mm"
include "3exp.mm"
include "reximdvai.mm"
include "mpd.mm"

theorem lcvat
  let wph: wff ph
  let cA: class A
  let cC: class C
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let vq: setvar q
  assume lcvat.s: |- S = ( LSubSp ` W )
  assume lcvat.p: |- .(+) = ( LSSum ` W )
  assume lcvat.a: |- A = ( LSAtoms ` W )
  assume icvat.c: |- C = ( <oL ` W )
  assume lcvat.w: |- ( ph -> W e. LMod )
  assume lcvat.t: |- ( ph -> T e. S )
  assume lcvat.u: |- ( ph -> U e. S )
  assume lcvat.l: |- ( ph -> T C U )

  disjoint A q
  disjoint S q
  disjoint T q
  disjoint U q
  disjoint W q
  disjoint ph q
  assert |- ( ph -> E. q e. A ( T .(+) q ) = U )

  proof
    wph
    cT
    cT
    vq
    cv
    #
    c.po
    co
    #
    wpss
    #
    @1
    cU
    wss
    #
    wa
    #
    vq
    cA
    wrex
    @1
    cU
    wceq
    #
    vq
    cA
    wrex
    wph
    cA
    c.po
    cS
    cT
    cU
    cW
    vq
    lcvat.s
    lcvat.p
    lcvat.a
    lcvat.w
    lcvat.t
    lcvat.u
    wph
    cC
    cS
    cT
    cU
    cW
    clmod
    lcvat.s
    icvat.c
    lcvat.w
    lcvat.t
    lcvat.u
    lcvat.l
    lcvpss
    lrelat
    wph
    @4
    @5
    vq
    cA
    wph
    @0
    cA
    wcel
    #
    @4
    @5
    wph
    @6
    @4
    w3a
    #
    cC
    cT
    cS
    cU
    @1
    cW
    clmod
    lcvat.s
    icvat.c
    wph
    @6
    cW
    clmod
    wcel
    #
    @4
    lcvat.w
    3ad2ant1
    #
    wph
    @6
    cT
    cS
    wcel
    #
    @4
    lcvat.t
    3ad2ant1
    #
    wph
    @6
    cU
    cS
    wcel
    @4
    lcvat.u
    3ad2ant1
    @7
    @8
    @10
    @0
    cS
    wcel
    @1
    cS
    wcel
    @9
    @11
    @7
    cA
    cS
    @0
    cW
    lcvat.s
    lcvat.a
    @9
    wph
    @6
    @4
    simp2
    lsatlssel
    c.po
    cS
    cT
    @0
    cW
    lcvat.s
    lcvat.p
    lsmcl
    syl3anc
    wph
    @6
    cT
    cU
    cC
    wbr
    @4
    lcvat.l
    3ad2ant1
    wph
    @6
    @2
    @3
    simp3l
    wph
    @6
    @2
    @3
    simp3r
    lcvnbtwn2
    3exp
    reximdvai
    mpd
end
