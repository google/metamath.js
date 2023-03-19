include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "mirinv.mm"
include "mpbiri.mm"

theorem mircinv
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
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirval.a: |- ( ph -> A e. P )
  assume mirfv.m: |- M = ( S ` A )


  assert |- ( ph -> ( M ` A ) = A )

  proof
    wph
    cA
    cM
    cfv
    cA
    wceq
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
end
