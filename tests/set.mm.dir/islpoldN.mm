include "wcel.mm"
include "cpw.mm"
include "wf.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "w3a.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wral.mm"
include "ex.mm"
include "alrimivv.mm"
include "jca.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "wb.mm"
include "islpolN.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem islpoldN
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cS: class S
  let cH: class H
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vo: setvar o
  assume lpolset.v: |- V = ( Base ` W )
  assume lpolset.s: |- S = ( LSubSp ` W )
  assume lpolset.z: |- .0. = ( 0g ` W )
  assume lpolset.a: |- A = ( LSAtoms ` W )
  assume lpolset.h: |- H = ( LSHyp ` W )
  assume lpolset.p: |- P = ( LPol ` W )
  assume islpold.w: |- ( ph -> W e. X )
  assume islpold.1: |- ( ph -> ._|_ : ~P V --> S )
  assume islpold.2: |- ( ph -> ( ._|_ ` V ) = { .0. } )
  assume islpold.3: |- ( ( ph /\ ( x C_ V /\ y C_ V /\ x C_ y ) ) -> ( ._|_ ` y ) C_ ( ._|_ ` x ) )
  assume islpold.4: |- ( ( ph /\ x e. A ) -> ( ._|_ ` x ) e. H )
  assume islpold.5: |- ( ( ph /\ x e. A ) -> ( ._|_ ` ( ._|_ ` x ) ) = x )

  disjoint A x
  disjoint x y
  disjoint W x
  disjoint W y
  disjoint ._|_ x
  disjoint ._|_ y
  disjoint ph x
  disjoint ph y
  disjoint w x
  disjoint A w
  disjoint H w
  disjoint o w
  disjoint S o
  disjoint S w
  disjoint V o
  disjoint V w
  disjoint o x
  disjoint o y
  disjoint W o
  disjoint w y
  disjoint W w
  disjoint .0. w
  disjoint A o
  disjoint H o
  disjoint ._|_ o
  disjoint .0. o
  assert |- ( ph -> ._|_ e. P )

  proof
    wph
    c.pe
    cP
    wcel
    #
    cV
    cpw
    cS
    c.pe
    wf
    #
    cV
    c.pe
    cfv
    c.0
    csn
    wceq
    #
    vx
    cv
    #
    cV
    wss
    vy
    cv
    #
    cV
    wss
    @3
    @4
    wss
    w3a
    #
    @4
    c.pe
    cfv
    @3
    c.pe
    cfv
    #
    wss
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @6
    cH
    wcel
    #
    @6
    c.pe
    cfv
    @3
    wceq
    #
    wa
    #
    vx
    cA
    wral
    #
    w3a
    #
    islpold.1
    wph
    @2
    @9
    @13
    islpold.2
    wph
    @8
    vx
    vy
    wph
    @5
    @7
    islpold.3
    ex
    alrimivv
    wph
    @12
    vx
    cA
    wph
    @3
    cA
    wcel
    wa
    @10
    @11
    islpold.4
    islpold.5
    jca
    ralrimiva
    3jca
    wph
    cW
    cX
    wcel
    @0
    @1
    @14
    wa
    wb
    islpold.w
    vx
    vy
    cA
    cP
    cS
    cH
    c.pe
    cV
    cW
    cX
    c.0
    lpolset.v
    lpolset.s
    lpolset.z
    lpolset.a
    lpolset.h
    lpolset.p
    islpolN
    syl
    mpbir2and
end
