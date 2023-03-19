include "cfv.mm"
include "mirf.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "eqid.mm"
include "co.mm"
include "eqeltrd.mm"
include "mircgr.mm"
include "mircgrs.mm"
include "wceq.mm"
include "a1i.mm"
include "fveq2d.mm"
include "syl6reqr.mm"
include "oveq12d.mm"
include "oveq12i.mm"
include "3eqtr4d.mm"
include "mirbtwn.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "mirbtwni.mm"
include "3eltr4g.mm"
include "ismir.mm"
include "eqcomd.mm"

theorem mirauto
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cT: class T
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume mirval.p: |- P = ( Base ` G )
  assume mirval.d: |- .- = ( dist ` G )
  assume mirval.i: |- I = ( Itv ` G )
  assume mirval.l: |- L = ( LineG ` G )
  assume mirval.s: |- S = ( pInvG ` G )
  assume mirval.g: |- ( ph -> G e. TarskiG )
  assume mirauto.m: |- M = ( S ` T )
  assume mirauto.x: |- X = ( M ` A )
  assume mirauto.y: |- Y = ( M ` B )
  assume mirauto.z: |- Z = ( M ` C )
  assume mirauto.0: |- ( ph -> T e. P )
  assume mirauto.1: |- ( ph -> A e. P )
  assume mirauto.2: |- ( ph -> B e. P )
  assume mirauto.3: |- ( ph -> C e. P )
  assume mirauto.4: |- ( ph -> ( ( S ` A ) ` B ) = C )


  assert |- ( ph -> ( ( S ` X ) ` Y ) = Z )

  proof
    wph
    cZ
    cY
    cX
    cS
    cfv
    #
    cfv
    wph
    cX
    cY
    cZ
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    wph
    cX
    cA
    cM
    cfv
    #
    cP
    mirauto.x
    wph
    cP
    cP
    cA
    cM
    wph
    cT
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
    mirauto.0
    mirauto.m
    mirf
    #
    mirauto.1
    ffvelrnd
    syl5eqel
    @0
    eqid
    wph
    cY
    cB
    cM
    cfv
    #
    cP
    mirauto.y
    wph
    cP
    cP
    cB
    cM
    @2
    mirauto.2
    ffvelrnd
    syl5eqel
    wph
    cZ
    cC
    cM
    cfv
    #
    cP
    mirauto.z
    wph
    cP
    cP
    cC
    cM
    @2
    mirauto.3
    ffvelrnd
    syl5eqel
    wph
    @1
    cB
    cA
    cS
    cfv
    #
    cfv
    #
    cM
    cfv
    #
    c.mi
    co
    @1
    @3
    c.mi
    co
    #
    cX
    cZ
    c.mi
    co
    cX
    cY
    c.mi
    co
    #
    wph
    cT
    cP
    cS
    cB
    cG
    cI
    cL
    cM
    c.mi
    cA
    @6
    cA
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirauto.0
    mirauto.m
    mirauto.1
    wph
    @6
    cC
    cP
    mirauto.4
    mirauto.3
    eqeltrd
    mirauto.1
    mirauto.2
    wph
    cA
    cB
    cP
    cS
    cG
    cI
    cL
    @5
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirauto.1
    @5
    eqid
    #
    mirauto.2
    mircgr
    mircgrs
    wph
    cX
    @1
    cZ
    @7
    c.mi
    cX
    @1
    wceq
    wph
    mirauto.x
    a1i
    wph
    @7
    @4
    cZ
    wph
    @6
    cC
    cM
    mirauto.4
    fveq2d
    mirauto.z
    syl6reqr
    oveq12d
    @9
    @8
    wceq
    wph
    cX
    @1
    cY
    @3
    c.mi
    mirauto.x
    mirauto.y
    oveq12i
    a1i
    3eqtr4d
    wph
    @1
    @4
    @3
    cI
    co
    cX
    cZ
    cY
    cI
    co
    wph
    cT
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cC
    cA
    cB
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirauto.0
    mirauto.m
    mirauto.3
    mirauto.1
    mirauto.2
    wph
    cA
    @6
    cB
    cI
    co
    cC
    cB
    cI
    co
    wph
    cA
    cB
    cP
    cS
    cG
    cI
    cL
    @5
    c.mi
    mirval.p
    mirval.d
    mirval.i
    mirval.l
    mirval.s
    mirval.g
    mirauto.1
    @10
    mirauto.2
    mirbtwn
    wph
    @6
    cC
    cB
    cI
    mirauto.4
    oveq1d
    eleqtrd
    mirbtwni
    mirauto.x
    cZ
    @4
    cY
    @3
    cI
    mirauto.z
    mirauto.y
    oveq12i
    3eltr4g
    ismir
    eqcomd
end
