include "ciin.mm"
include "cuni.mm"
include "cdif.mm"
include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "wss.mm"
include "wceq.mm"
include "elssuni.mm"
include "syl.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqcomd.mm"
include "incom.mm"
include "a1i.mm"
include "dfin4.mm"
include "3eqtrd.mm"
include "iineq2dv.mm"
include "c0.mm"
include "wne.mm"
include "iindif2.mm"
include "eqtrd.mm"
include "csalg.mm"
include "adantr.mm"
include "saldifcl.mm"
include "syl2anc.mm"
include "saliuncl.mm"
include "eqeltrd.mm"

theorem saliincl
  let wph: wff ph
  let cS: class S
  let vk: setvar k
  let cE: class E
  let cK: class K
  let vx: setvar x
  assume saliincl.s: |- ( ph -> S e. SAlg )
  assume saliincl.kct: |- ( ph -> K ~<_ _om )
  assume saliincl.kn0: |- ( ph -> K =/= (/) )
  assume saliincl.e: |- ( ( ph /\ k e. K ) -> E e. S )

  disjoint K k
  disjoint S k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> |^|_ k e. K E e. S )

  proof
    wph
    vk
    cK
    cE
    ciin
    #
    cS
    cuni
    #
    vk
    cK
    @1
    cE
    cdif
    #
    ciun
    #
    cdif
    #
    cS
    wph
    @0
    vk
    cK
    @1
    @2
    cdif
    #
    ciin
    #
    @4
    wph
    vk
    cK
    cE
    @5
    wph
    vk
    cv
    cK
    wcel
    #
    wa
    #
    cE
    cE
    @1
    cin
    #
    @1
    cE
    cin
    #
    @5
    @8
    @9
    cE
    @8
    cE
    @1
    wss
    #
    @9
    cE
    wceq
    @8
    cE
    cS
    wcel
    #
    @11
    saliincl.e
    cE
    cS
    elssuni
    syl
    cE
    @1
    df-ss
    sylib
    eqcomd
    @9
    @10
    wceq
    @8
    cE
    @1
    incom
    a1i
    @10
    @5
    wceq
    @8
    @1
    cE
    dfin4
    a1i
    3eqtrd
    iineq2dv
    wph
    cK
    c0
    wne
    @6
    @4
    wceq
    saliincl.kn0
    vk
    cK
    @1
    @2
    iindif2
    syl
    eqtrd
    wph
    cS
    csalg
    wcel
    #
    @3
    cS
    wcel
    @4
    cS
    wcel
    saliincl.s
    wph
    cS
    vk
    @2
    cK
    saliincl.s
    saliincl.kct
    @8
    @13
    @12
    @2
    cS
    wcel
    wph
    @13
    @7
    saliincl.s
    adantr
    saliincl.e
    cS
    cE
    saldifcl
    syl2anc
    saliuncl
    cS
    @3
    saldifcl
    syl2anc
    eqeltrd
end
