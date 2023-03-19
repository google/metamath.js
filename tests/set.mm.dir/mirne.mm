include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "mirmir.mm"
include "adantr.mm"
include "eqid.mm"
include "mirinv.mm"
include "mpbiri.mm"
include "3eqtr3d.mm"
include "wne.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "neqned.mm"

theorem mirne
  let wph: wff ph
  let cA: class A
  let cB: class B
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
  let cC: class C
  let vg: setvar g
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirval.a: |- ( ph -> A e. P )
  assume mirfv.m: |- M = ( S ` A )
  assume mirinv.b: |- ( ph -> B e. P )
  assume mirne.1: |- ( ph -> B =/= A )


  assert |- ( ph -> ( M ` B ) =/= A )

  proof
    wph
    cB
    cM
    cfv
    #
    cA
    wph
    @0
    cA
    wceq
    #
    cB
    cA
    wceq
    wph
    @1
    wa
    #
    @0
    cM
    cfv
    #
    cA
    cM
    cfv
    #
    cB
    cA
    @2
    @0
    cA
    cM
    wph
    @1
    simpr
    fveq2d
    wph
    @3
    cB
    wceq
    @1
    wph
    cA
    cB
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
    mirinv.b
    mirmir
    adantr
    wph
    @4
    cA
    wceq
    #
    @1
    wph
    @5
    cA
    cA
    wceq
    cA
    eqid
    wph
    cA
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
    mirval.a
    mirinv
    mpbiri
    adantr
    3eqtr3d
    @2
    cB
    cA
    wph
    cB
    cA
    wne
    @1
    mirne.1
    adantr
    neneqd
    pm2.65da
    neqned
end
