include "cfv.mm"
include "wceq.mm"
include "ccgrg.mm"
include "eqid.mm"
include "mircl.mm"
include "cs3.mm"
include "crag.mm"
include "wcel.mm"
include "co.mm"
include "israg.mm"
include "mpbid.mm"
include "tgidinside.mm"
include "eqcomd.mm"
include "mirinv.mm"

theorem ragflat2
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
  assume ragflat2.d: |- ( ph -> D e. P )
  assume ragflat2.1: |- ( ph -> <" A B C "> e. ( raG ` G ) )
  assume ragflat2.2: |- ( ph -> <" D B C "> e. ( raG ` G ) )
  assume ragflat2.3: |- ( ph -> C e. ( A I D ) )


  assert |- ( ph -> B = C )

  proof
    wph
    cC
    cB
    cS
    cfv
    #
    cfv
    #
    cC
    wceq
    cB
    cC
    wceq
    wph
    cC
    @1
    wph
    @1
    cA
    cP
    cG
    ccgrg
    cfv
    #
    cG
    cI
    cL
    c.mi
    cA
    cD
    cC
    israg.p
    israg.l
    israg.i
    israg.g
    israg.a
    ragflat2.d
    israg.c
    @2
    eqid
    wph
    cB
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    cC
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.b
    @0
    eqid
    #
    israg.c
    mircl
    israg.a
    israg.d
    ragflat2.3
    wph
    cA
    cB
    cC
    cs3
    cG
    crag
    cfv
    #
    wcel
    cA
    cC
    c.mi
    co
    cA
    @1
    c.mi
    co
    wceq
    ragflat2.1
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
    wph
    cD
    cB
    cC
    cs3
    @4
    wcel
    cD
    cC
    c.mi
    co
    cD
    @1
    c.mi
    co
    wceq
    ragflat2.2
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
    ragflat2.d
    israg.b
    israg.c
    israg
    mpbid
    tgidinside
    eqcomd
    wph
    cB
    cC
    cP
    cS
    cG
    cI
    cL
    @0
    c.mi
    israg.p
    israg.d
    israg.i
    israg.l
    israg.s
    israg.g
    israg.b
    @3
    israg.c
    mirinv
    mpbid
end
