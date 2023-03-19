include "cs3.mm"
include "crag.mm"
include "cfv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "ccgrg.mm"
include "eqid.mm"
include "mircl.mm"
include "necomd.mm"
include "mircgr.mm"
include "eqcomd.mm"
include "israg.mm"
include "mpbid.mm"
include "lncgr.mm"
include "mpbird.mm"

theorem ragcol
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
  assume ragcol.d: |- ( ph -> D e. P )
  assume ragcol.1: |- ( ph -> <" A B C "> e. ( raG ` G ) )
  assume ragcol.2: |- ( ph -> A =/= B )
  assume ragcol.3: |- ( ph -> ( A e. ( B L D ) \/ B = D ) )


  assert |- ( ph -> <" D B C "> e. ( raG ` G ) )

  proof
    wph
    cD
    cB
    cC
    cs3
    cG
    crag
    cfv
    #
    wcel
    cD
    cC
    c.mi
    co
    cD
    cC
    cB
    cS
    cfv
    #
    cfv
    #
    c.mi
    co
    wceq
    wph
    cC
    @2
    cP
    cG
    ccgrg
    cfv
    #
    cG
    cI
    cL
    c.mi
    cB
    cA
    cD
    israg.p
    israg.l
    israg.i
    israg.g
    israg.b
    israg.a
    ragcol.d
    @3
    eqid
    israg.c
    wph
    cB
    cP
    cS
    cG
    cI
    cL
    @1
    c.mi
    cC
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.b
    @1
    eqid
    #
    israg.c
    mircl
    israg.d
    wph
    cA
    cB
    ragcol.2
    necomd
    ragcol.3
    wph
    cB
    @2
    c.mi
    co
    cB
    cC
    c.mi
    co
    wph
    cB
    cC
    cP
    cS
    cG
    cI
    cL
    @1
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.b
    @4
    israg.c
    mircgr
    eqcomd
    wph
    cA
    cB
    cC
    cs3
    @0
    wcel
    cA
    cC
    c.mi
    co
    cA
    @2
    c.mi
    co
    wceq
    ragcol.1
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
    lncgr
    wph
    cD
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
    ragcol.d
    israg.b
    israg.c
    israg
    mpbird
end
