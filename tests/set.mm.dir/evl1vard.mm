include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "ccrg.mm"
include "crg.mm"
include "crngring.mm"
include "vr1cl.mm"
include "3syl.mm"
include "cid.mm"
include "cres.mm"
include "evl1var.mm"
include "syl.mm"
include "fveq1d.mm"
include "fvresi.mm"
include "eqtrd.mm"
include "jca.mm"

theorem evl1vard
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cR: class R
  let cU: class U
  let cO: class O
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  assume evl1var.q: |- O = ( eval1 ` R )
  assume evl1var.v: |- X = ( var1 ` R )
  assume evl1var.b: |- B = ( Base ` R )
  assume evl1vard.p: |- P = ( Poly1 ` R )
  assume evl1vard.u: |- U = ( Base ` P )
  assume evl1vard.1: |- ( ph -> R e. CRing )
  assume evl1vard.2: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X e. U /\ ( ( O ` X ) ` Y ) = Y ) )

  proof
    wph
    cX
    cU
    wcel
    #
    cY
    cX
    cO
    cfv
    #
    cfv
    #
    cY
    wceq
    wph
    cR
    ccrg
    wcel
    #
    cR
    crg
    wcel
    @0
    evl1vard.1
    cR
    crngring
    cU
    cP
    cR
    cX
    evl1var.v
    evl1vard.p
    evl1vard.u
    vr1cl
    3syl
    wph
    @2
    cY
    cid
    cB
    cres
    #
    cfv
    #
    cY
    wph
    cY
    @1
    @4
    wph
    @3
    @1
    @4
    wceq
    evl1vard.1
    cB
    cR
    cO
    cX
    evl1var.q
    evl1var.v
    evl1var.b
    evl1var
    syl
    fveq1d
    wph
    cY
    cB
    wcel
    @5
    cY
    wceq
    evl1vard.2
    cB
    cY
    fvresi
    syl
    eqtrd
    jca
end
