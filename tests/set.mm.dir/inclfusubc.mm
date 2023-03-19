include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cidfu.mm"
include "cfv.mm"
include "wcel.mm"
include "cfth.mm"
include "fthfunc.mm"
include "csubc.mm"
include "eqid.mm"
include "rescfth.mm"
include "syl.mm"
include "sseldi.mm"
include "cop.mm"
include "df-br.mm"
include "cid.mm"
include "cres.mm"
include "cv.mm"
include "cmpt2.mm"
include "opeq12d.mm"
include "wceq.mm"
include "idfusubc.mm"
include "eqtr4d.mm"
include "eleq1d.mm"
include "syl5bb.mm"
include "mpbird.mm"

theorem inclfusubc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let vk: setvar k
  assume inclfusubc.j: |- ( ph -> J e. ( Subcat ` C ) )
  assume inclfusubc.s: |- S = ( C |`cat J )
  assume inclfusubc.b: |- B = ( Base ` S )
  assume inclfusubc.f: |- ( ph -> F = ( _I |` B ) )
  assume inclfusubc.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( x J y ) ) ) )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint J x
  disjoint J y
  disjoint S x
  disjoint S y
  disjoint k x
  assert |- ( ph -> F ( S Func C ) G )

  proof
    wph
    cF
    cG
    cS
    cC
    cfunc
    co
    #
    wbr
    #
    cS
    cidfu
    cfv
    #
    @0
    wcel
    #
    wph
    cS
    cC
    cfth
    co
    #
    @0
    @2
    cS
    cC
    fthfunc
    wph
    cJ
    cC
    csubc
    cfv
    wcel
    #
    @2
    @4
    wcel
    inclfusubc.j
    cC
    cS
    @2
    cJ
    inclfusubc.s
    @2
    eqid
    #
    rescfth
    syl
    sseldi
    @1
    cF
    cG
    cop
    #
    @0
    wcel
    wph
    @3
    cF
    cG
    @0
    df-br
    wph
    @7
    @2
    @0
    wph
    @7
    cid
    cB
    cres
    #
    vx
    vy
    cB
    cB
    cid
    vx
    cv
    vy
    cv
    cJ
    co
    cres
    cmpt2
    #
    cop
    #
    @2
    wph
    cF
    @8
    cG
    @9
    inclfusubc.f
    inclfusubc.g
    opeq12d
    wph
    @5
    @2
    @10
    wceq
    inclfusubc.j
    vx
    vy
    cB
    cC
    cS
    @2
    cJ
    inclfusubc.s
    @6
    inclfusubc.b
    idfusubc
    syl
    eqtr4d
    eleq1d
    syl5bb
    mpbird
end
