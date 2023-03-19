include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "crab.mm"
include "clt.mm"
include "wbr.mm"
include "cin.mm"
include "crest.mm"
include "cv.mm"
include "wa.mm"
include "cr.mm"
include "cmpt.mm"
include "cdm.mm"
include "wf.mm"
include "eqid.mm"
include "smff.mm"
include "dmmptdf.mm"
include "feq2d.mm"
include "mpbid.mm"
include "fvmptelrn.mm"
include "rexrd.mm"
include "pimiooltgt.mm"
include "subsalsal.mm"
include "smfpimltxrmpt.mm"
include "smfpimgtxrmpt.mm"
include "salincld.mm"
include "eqeltrd.mm"

theorem smfpimioompt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cL: class L
  let cV: class V
  let cW: class W
  let vk: setvar k
  assume smfpimioompt.x: |- F/ x ph
  assume smfpimioompt.s: |- ( ph -> S e. SAlg )
  assume smfpimioompt.a: |- ( ph -> A e. V )
  assume smfpimioompt.b: |- ( ( ph /\ x e. A ) -> B e. W )
  assume smfpimioompt.m: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfpimioompt.l: |- ( ph -> L e. RR* )
  assume smfpimioompt.r: |- ( ph -> R e. RR* )

  disjoint A x
  disjoint L x
  disjoint R x
  disjoint k x
  assert |- ( ph -> { x e. A | B e. ( L (,) R ) } e. ( S |`t A ) )

  proof
    wph
    cB
    cL
    cR
    cioo
    co
    wcel
    vx
    cA
    crab
    cB
    cR
    clt
    wbr
    vx
    cA
    crab
    #
    cL
    cB
    clt
    wbr
    vx
    cA
    crab
    #
    cin
    cS
    cA
    crest
    co
    #
    wph
    vx
    cA
    cB
    cR
    cL
    smfpimioompt.x
    smfpimioompt.l
    smfpimioompt.r
    wph
    vx
    cv
    cA
    wcel
    wa
    cB
    wph
    vx
    cA
    cB
    cr
    wph
    vx
    cA
    cB
    cmpt
    #
    cdm
    #
    cr
    @3
    wf
    cA
    cr
    @3
    wf
    wph
    @4
    cS
    @3
    smfpimioompt.s
    smfpimioompt.m
    @4
    eqid
    smff
    wph
    @4
    cA
    cr
    @3
    wph
    vx
    @3
    cA
    cB
    cW
    smfpimioompt.x
    @3
    eqid
    smfpimioompt.b
    dmmptdf
    feq2d
    mpbid
    fvmptelrn
    rexrd
    pimiooltgt
    wph
    @2
    @0
    @1
    wph
    cA
    cS
    @2
    cV
    smfpimioompt.s
    smfpimioompt.a
    @2
    eqid
    subsalsal
    wph
    vx
    cA
    cB
    cR
    cS
    cW
    smfpimioompt.x
    smfpimioompt.s
    smfpimioompt.b
    smfpimioompt.m
    smfpimioompt.r
    smfpimltxrmpt
    wph
    vx
    cA
    cB
    cS
    cL
    cW
    smfpimioompt.x
    smfpimioompt.s
    smfpimioompt.b
    smfpimioompt.m
    smfpimioompt.l
    smfpimgtxrmpt
    salincld
    eqeltrd
end
