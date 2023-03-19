include "cfv.mm"
include "mircl.mm"
include "co.mm"
include "mircgr.mm"
include "eqcomd.mm"
include "mirbtwn.mm"
include "tgbtwncom.mm"
include "ismir.mm"

theorem mirmir
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
  assume mirmir.b: |- ( ph -> B e. P )


  assert |- ( ph -> ( M ` ( M ` B ) ) = B )

  proof
    wph
    cB
    cB
    cM
    cfv
    #
    cM
    cfv
    wph
    cA
    @0
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
    wph
    cA
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cB
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirval.a
    mirfv.m
    mirmir.b
    mircl
    #
    mirmir.b
    wph
    cA
    @0
    c.mi
    co
    cA
    cB
    c.mi
    co
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
    mircgr
    eqcomd
    wph
    @0
    cA
    cB
    cP
    cG
    cI
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.g
    @1
    mirval.a
    mirmir.b
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
    mirbtwn
    tgbtwncom
    ismir
    eqcomd
end
