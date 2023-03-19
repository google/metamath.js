include "cfv.mm"
include "fveq2d.mm"
include "mirmir.mm"
include "eqtr3d.mm"

theorem mircom
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
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
  let vg: setvar g
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirval.a: |- ( ph -> A e. P )
  assume mirfv.m: |- M = ( S ` A )
  assume mirmir.b: |- ( ph -> B e. P )
  assume mircom.1: |- ( ph -> ( M ` B ) = C )


  assert |- ( ph -> ( M ` C ) = B )

  proof
    wph
    cB
    cM
    cfv
    #
    cM
    cfv
    cC
    cM
    cfv
    cB
    wph
    @0
    cC
    cM
    mircom.1
    fveq2d
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
    mirmir.b
    mirmir
    eqtr3d
end
