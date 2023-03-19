include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cif.mm"
include "breq2d.mm"
include "pm5.32da.mm"
include "ifbid.mm"
include "wceq.mm"
include "adantrr.mm"
include "ifeq1da.mm"
include "eqtrd.mm"

theorem ibllem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume ibllem.1: |- ( ( ph /\ x e. A ) -> B = C )


  assert |- ( ph -> if ( ( x e. A /\ 0 <_ B ) , B , 0 ) = if ( ( x e. A /\ 0 <_ C ) , C , 0 ) )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    cB
    cc0
    cif
    @0
    cc0
    cC
    cle
    wbr
    #
    wa
    #
    cB
    cc0
    cif
    @4
    cC
    cc0
    cif
    wph
    @2
    @4
    cB
    cc0
    wph
    @0
    @1
    @3
    wph
    @0
    wa
    cB
    cC
    cc0
    cle
    ibllem.1
    breq2d
    pm5.32da
    ifbid
    wph
    @4
    cB
    cC
    cc0
    wph
    @0
    cB
    cC
    wceq
    @3
    ibllem.1
    adantrr
    ifeq1da
    eqtrd
end
