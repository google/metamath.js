include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cwun.mm"
include "adantr.mm"
include "simpr.mm"
include "wunop.mm"
include "wunsn.mm"
include "syl5eqel.mm"

theorem 1strwunbndx
  let wph: wff ph
  let cB: class B
  let cU: class U
  let cG: class G
  assume 1str.g: |- G = { <. ( Base ` ndx ) , B >. }
  assume 1strwun.u: |- ( ph -> U e. WUni )
  assume 1strwunbndx.b: |- ( ph -> ( Base ` ndx ) e. U )


  assert |- ( ( ph /\ B e. U ) -> G e. U )

  proof
    wph
    cB
    cU
    wcel
    #
    wa
    #
    cG
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    csn
    cU
    1str.g
    @1
    @3
    cU
    wph
    cU
    cwun
    wcel
    @0
    1strwun.u
    adantr
    #
    @1
    @2
    cB
    cU
    @4
    wph
    @2
    cU
    wcel
    @0
    1strwunbndx.b
    adantr
    wph
    @0
    simpr
    wunop
    wunsn
    syl5eqel
end
