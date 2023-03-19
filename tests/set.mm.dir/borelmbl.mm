include "cvv.mm"
include "crrx.mm"
include "cfv.mm"
include "ctopn.mm"
include "fvexd.mm"
include "dmovnsal.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "adantr.mm"
include "simpr.mm"
include "opnvonmbl.mm"
include "ssd.mm"
include "cvoln.mm"
include "cdm.mm"
include "cuni.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "eqid.mm"
include "unidmvon.mm"
include "wceq.mm"
include "unieqi.mm"
include "a1i.mm"
include "rrxunitopnfi.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "salgenss.mm"

theorem borelmbl
  let wph: wff ph
  let cB: class B
  let cS: class S
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x
  assume borelmbl.x: |- ( ph -> X e. Fin )
  assume borelmbl.s: |- S = dom ( voln ` X )
  assume borelmbl.b: |- B = ( SalGen ` ( TopOpen ` ( RR^ ` X ) ) )


  assert |- ( ph -> B C_ S )

  proof
    wph
    cS
    cB
    cvv
    cX
    crrx
    cfv
    #
    ctopn
    cfv
    #
    wph
    @0
    ctopn
    fvexd
    borelmbl.b
    wph
    cS
    cX
    borelmbl.x
    borelmbl.s
    dmovnsal
    wph
    vy
    @1
    cS
    wph
    vy
    cv
    #
    @1
    wcel
    #
    wa
    cS
    @2
    cX
    wph
    cX
    cfn
    wcel
    #
    @3
    borelmbl.x
    adantr
    borelmbl.s
    wph
    @3
    simpr
    opnvonmbl
    ssd
    wph
    cX
    cvoln
    cfv
    cdm
    #
    cuni
    #
    cr
    cX
    cmap
    co
    #
    cS
    cuni
    #
    @1
    cuni
    #
    wph
    @5
    cX
    borelmbl.x
    @5
    eqid
    unidmvon
    @8
    @6
    wceq
    wph
    cS
    @5
    borelmbl.s
    unieqi
    a1i
    wph
    @4
    @9
    @7
    wceq
    borelmbl.x
    cX
    rrxunitopnfi
    syl
    3eqtr4d
    salgenss
end
