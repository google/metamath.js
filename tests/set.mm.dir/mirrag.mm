include "cfv.mm"
include "cs3.mm"
include "crag.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "mircl.mm"
include "israg.mm"
include "mpbid.mm"
include "mircgrs.mm"
include "mirmir2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "mpbird.mm"

theorem mirrag
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let vg: setvar g
  let vw: setvar w
  assume israg.p: |- P = ( Base ` G )
  assume israg.d: |- .- = ( dist ` G )
  assume israg.i: |- I = ( Itv ` G )
  assume israg.l: |- L = ( LineG ` G )
  assume israg.s: |- S = ( pInvG ` G )
  assume israg.g: |- ( ph -> G e. TarskiG )
  assume israg.a: |- ( ph -> A e. P )
  assume israg.b: |- ( ph -> B e. P )
  assume israg.c: |- ( ph -> C e. P )
  assume ragmir.1: |- ( ph -> <" A B C "> e. ( raG ` G ) )
  assume mirrag.m: |- M = ( S ` D )
  assume mirrag.d: |- ( ph -> D e. P )


  assert |- ( ph -> <" ( M ` A ) ( M ` B ) ( M ` C ) "> e. ( raG ` G ) )

  proof
    wph
    cA
    cM
    cfv
    #
    cB
    cM
    cfv
    #
    cC
    cM
    cfv
    #
    cs3
    cG
    crag
    cfv
    #
    wcel
    @0
    @2
    c.mi
    co
    #
    @0
    @2
    @1
    cS
    cfv
    cfv
    #
    c.mi
    co
    #
    wceq
    wph
    @4
    @0
    cC
    cB
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
    @6
    wph
    cD
    cP
    cS
    @8
    cG
    cI
    cL
    cM
    c.mi
    cA
    cC
    cA
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    mirrag.d
    mirrag.m
    israg.a
    israg.c
    israg.a
    wph
    cB
    cP
    cS
    cG
    cI
    cL
    @7
    c.mi
    cC
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.b
    @7
    eqid
    israg.c
    mircl
    wph
    cA
    cB
    cC
    cs3
    @3
    wcel
    cA
    cC
    c.mi
    co
    cA
    @8
    c.mi
    co
    wceq
    ragmir.1
    wph
    cA
    cB
    cC
    cP
    cS
    cG
    cI
    cL
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.a
    israg.b
    israg.c
    israg
    mpbid
    mircgrs
    wph
    @9
    @5
    @0
    c.mi
    wph
    cD
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cC
    cB
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    mirrag.d
    mirrag.m
    israg.c
    israg.b
    mirmir2
    oveq2d
    eqtrd
    wph
    @0
    @1
    @2
    cP
    cS
    cG
    cI
    cL
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    wph
    cD
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cA
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    mirrag.d
    mirrag.m
    israg.a
    mircl
    wph
    cD
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cB
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    mirrag.d
    mirrag.m
    israg.b
    mircl
    wph
    cD
    cP
    cS
    cG
    cI
    cL
    cM
    c.mi
    cC
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    mirrag.d
    mirrag.m
    israg.c
    mircl
    israg
    mpbird
end
