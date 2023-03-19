include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "cfv.mm"
include "simpr.mm"
include "fveq2d.mm"
include "3eqtr4g.mm"
include "fveq1d.mm"
include "mirmir.mm"
include "adantr.mm"
include "3eqtr3rd.mm"
include "wb.mm"
include "mirinv.mm"
include "mpbid.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"
include "neqned.mm"

theorem colperpexlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cG: class G
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  assume colperpex.p: |- P = ( Base ` G )
  assume colperpex.d: |- .- = ( dist ` G )
  assume colperpex.i: |- I = ( Itv ` G )
  assume colperpex.l: |- L = ( LineG ` G )
  assume colperpex.g: |- ( ph -> G e. TarskiG )
  assume colperpexlem.s: |- S = ( pInvG ` G )
  assume colperpexlem.m: |- M = ( S ` A )
  assume colperpexlem.n: |- N = ( S ` B )
  assume colperpexlem.k: |- K = ( S ` Q )
  assume colperpexlem.a: |- ( ph -> A e. P )
  assume colperpexlem.b: |- ( ph -> B e. P )
  assume colperpexlem.c: |- ( ph -> C e. P )
  assume colperpexlem.q: |- ( ph -> Q e. P )
  assume colperpexlem.1: |- ( ph -> <" A B C "> e. ( raG ` G ) )
  assume colperpexlem.2: |- ( ph -> ( K ` ( M ` C ) ) = ( N ` C ) )
  assume colperpexlem2.e: |- ( ph -> B =/= C )


  assert |- ( ph -> A =/= Q )

  proof
    wph
    cA
    cQ
    wph
    cB
    cC
    wne
    cA
    cQ
    wceq
    #
    wn
    colperpexlem2.e
    wph
    @0
    cB
    cC
    wph
    @0
    cB
    cC
    wceq
    #
    wph
    @0
    wa
    #
    cC
    cN
    cfv
    #
    cC
    wceq
    #
    @1
    @2
    cC
    cM
    cfv
    #
    cM
    cfv
    #
    @5
    cK
    cfv
    #
    cC
    @3
    @2
    @5
    cM
    cK
    @2
    cA
    cS
    cfv
    cQ
    cS
    cfv
    cM
    cK
    @2
    cA
    cQ
    cS
    wph
    @0
    simpr
    fveq2d
    colperpexlem.m
    colperpexlem.k
    3eqtr4g
    fveq1d
    wph
    @6
    cC
    wceq
    @0
    wph
    cA
    cC
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    colperpexlem.s
    colperpex.g
    colperpexlem.a
    colperpexlem.m
    colperpexlem.c
    mirmir
    adantr
    wph
    @7
    @3
    wceq
    @0
    colperpexlem.2
    adantr
    3eqtr3rd
    wph
    @4
    @1
    wb
    @0
    wph
    cB
    cC
    cP
    cS
    cG
    cI
    cL
    cN
    c.mi
    colperpex.p
    colperpex.d
    colperpex.i
    colperpex.l
    colperpexlem.s
    colperpex.g
    colperpexlem.b
    colperpexlem.n
    colperpexlem.c
    mirinv
    adantr
    mpbid
    ex
    necon3ad
    mpd
    neqned
end
