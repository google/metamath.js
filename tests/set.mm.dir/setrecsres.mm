include "cpw.mm"
include "cres.mm"
include "csetrecs.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "wa.mm"
include "wceq.mm"
include "id.mm"
include "resss.mm"
include "a1i.mm"
include "setrecsss.mm"
include "syl6sseqr.mm"
include "sylan9ssr.mm"
include "wcel.mm"
include "selpw.mm"
include "fvres.mm"
include "sylbir.mm"
include "syl.mm"
include "eqid.mm"
include "cvv.mm"
include "vex.mm"
include "setrec1.mm"
include "adantl.mm"
include "eqsstr3d.mm"
include "ex.mm"
include "alrimiv.mm"
include "setrec2v.mm"
include "eqssd.mm"

theorem setrecsres
  let wph: wff ph
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vk: setvar k
  assume setrecsres.1: |- B = setrecs ( F )
  assume setrecsres.2: |- ( ph -> Fun F )


  assert |- ( ph -> B = setrecs ( ( F |` ~P B ) ) )

  proof
    wph
    cB
    cF
    cB
    cpw
    #
    cres
    #
    csetrecs
    #
    wph
    cB
    @2
    cF
    vx
    setrecsres.1
    wph
    vx
    cv
    #
    @2
    wss
    #
    @3
    cF
    cfv
    #
    @2
    wss
    #
    wi
    vx
    wph
    @4
    @6
    wph
    @4
    wa
    #
    @5
    @3
    @1
    cfv
    #
    @2
    @7
    @3
    cB
    wss
    #
    @8
    @5
    wceq
    #
    @4
    wph
    @3
    @2
    cB
    @4
    id
    #
    wph
    @2
    cF
    csetrecs
    cB
    wph
    @1
    cF
    setrecsres.2
    @1
    cF
    wss
    wph
    cF
    @0
    resss
    a1i
    setrecsss
    setrecsres.1
    syl6sseqr
    #
    sylan9ssr
    @9
    @3
    @0
    wcel
    @10
    vx
    cB
    selpw
    @3
    @0
    cF
    fvres
    sylbir
    syl
    @4
    @8
    @2
    wss
    wph
    @4
    @3
    @2
    @1
    @2
    eqid
    @3
    cvv
    wcel
    @4
    vx
    vex
    a1i
    @11
    setrec1
    adantl
    eqsstr3d
    ex
    alrimiv
    setrec2v
    @12
    eqssd
end
