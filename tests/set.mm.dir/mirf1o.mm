include "wfn.mm"
include "ccnv.mm"
include "wceq.mm"
include "wf1o.mm"
include "wf.mm"
include "mirf.mm"
include "ffn.mm"
include "syl.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "mirmir.mm"
include "ralrimiva.mm"
include "nvocnv.mm"
include "syl2anc.mm"
include "nvof1o.mm"

theorem mirf1o
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let vg: setvar g
  let va: setvar a
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirval.a: |- ( ph -> A e. P )
  assume mirfv.m: |- M = ( S ` A )


  assert |- ( ph -> M : P -1-1-onto-> P )

  proof
    wph
    cM
    cP
    wfn
    #
    cM
    ccnv
    cM
    wceq
    #
    cP
    cP
    cM
    wf1o
    wph
    cP
    cP
    cM
    wf
    #
    @0
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    mirf
    #
    cP
    cP
    cM
    ffn
    syl
    wph
    @2
    va
    cv
    #
    cM
    cfv
    cM
    cfv
    @4
    wceq
    #
    va
    cP
    wral
    @1
    @3
    wph
    @5
    va
    cP
    wph
    @4
    cP
    wcel
    #
    wa
    cA
    @4
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    wph
    cG
    cstrkg
    wcel
    @6
    mirval.g
    adantr
    wph
    cA
    cP
    wcel
    @6
    mirval.a
    adantr
    mirfv.m
    wph
    @6
    simpr
    mirmir
    ralrimiva
    va
    cP
    cM
    nvocnv
    syl2anc
    cP
    cM
    nvof1o
    syl2anc
end
