include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "ccnp.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "cc.mm"
include "wf.mm"
include "climc.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "limclner.mm"
include "ne0i.mm"
include "necon2bi.mm"
include "syl.mm"
include "intnand.mm"
include "wss.mm"
include "wb.mm"
include "ax-resscn.mm"
include "eqid.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "crest.mm"
include "tgioo2.mm"
include "eqtri.mm"
include "cnplimc.mm"
include "sylancr.mm"
include "mtbird.mm"

theorem jumpncnp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let vk: setvar k
  let vx: setvar x
  assume jumpncnp.k: |- K = ( TopOpen ` CCfld )
  assume jumpncnp.a: |- ( ph -> A C_ RR )
  assume jumpncnp.3: |- J = ( topGen ` ran (,) )
  assume jumpncnp.f: |- ( ph -> F : A --> CC )
  assume jumpncnp.b: |- ( ph -> B e. RR )
  assume jumpncnp.lpt1: |- ( ph -> B e. ( ( limPt ` J ) ` ( A i^i ( -oo (,) B ) ) ) )
  assume jumpncnp.lpt2: |- ( ph -> B e. ( ( limPt ` J ) ` ( A i^i ( B (,) +oo ) ) ) )
  assume jumpncnp.8: |- ( ph -> L e. ( ( F |` ( -oo (,) B ) ) limCC B ) )
  assume jumpncnp.9: |- ( ph -> R e. ( ( F |` ( B (,) +oo ) ) limCC B ) )
  assume jumpncnp.lner: |- ( ph -> L =/= R )


  assert |- ( ph -> -. F e. ( ( J CnP ( TopOpen ` CCfld ) ) ` B ) )

  proof
    wph
    cF
    cB
    cJ
    ccnfld
    ctopn
    cfv
    #
    ccnp
    co
    cfv
    wcel
    #
    cr
    cc
    cF
    wf
    #
    cB
    cF
    cfv
    #
    cF
    cB
    climc
    co
    #
    wcel
    #
    wa
    #
    wph
    @5
    @2
    wph
    @4
    c0
    wceq
    @5
    wn
    wph
    cA
    cB
    cR
    cF
    cJ
    cK
    cL
    jumpncnp.k
    jumpncnp.a
    jumpncnp.3
    jumpncnp.f
    jumpncnp.lpt1
    jumpncnp.lpt2
    jumpncnp.8
    jumpncnp.9
    jumpncnp.lner
    limclner
    @5
    @4
    c0
    @4
    @3
    ne0i
    necon2bi
    syl
    intnand
    wph
    cr
    cc
    wss
    cB
    cr
    wcel
    @1
    @6
    wb
    ax-resscn
    jumpncnp.b
    cr
    cB
    cF
    cJ
    @0
    @0
    eqid
    #
    cJ
    cioo
    crn
    ctg
    cfv
    @0
    cr
    crest
    co
    jumpncnp.3
    @0
    @7
    tgioo2
    eqtri
    cnplimc
    sylancr
    mtbird
end
