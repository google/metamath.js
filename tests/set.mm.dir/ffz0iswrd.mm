include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cword.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "cfzo.mm"
include "fzval3.mm"
include "feq2d.mm"
include "biimpa.mm"
include "iswrdi.mm"
include "syl.mm"
include "wn.mm"
include "c0.mm"
include "wnel.mm"
include "wo.mm"
include "wceq.mm"
include "df-nel.mm"
include "biimpri.mm"
include "olcd.mm"
include "fz0.mm"
include "iswrddm0.mm"
include "syl6bi.mm"
include "imp.mm"
include "pm2.61ian.mm"

theorem ffz0iswrd
  let cS: class S
  let cL: class L
  let cW: class W


  assert |- ( W : ( 0 ... L ) --> S -> W e. Word S )

  proof
    cL
    cz
    wcel
    #
    cc0
    cL
    cfz
    co
    #
    cS
    cW
    wf
    #
    cW
    cS
    cword
    wcel
    #
    @0
    @2
    wa
    cc0
    cL
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cS
    cW
    wf
    #
    @3
    @0
    @2
    @6
    @0
    @1
    @5
    cS
    cW
    cc0
    cL
    fzval3
    feq2d
    biimpa
    cS
    @4
    cW
    iswrdi
    syl
    @0
    wn
    #
    @2
    @3
    @7
    @2
    c0
    cS
    cW
    wf
    @3
    @7
    @1
    c0
    cS
    cW
    @7
    cc0
    cz
    wnel
    #
    cL
    cz
    wnel
    #
    wo
    @1
    c0
    wceq
    @7
    @9
    @8
    @9
    @7
    cL
    cz
    df-nel
    biimpri
    olcd
    cc0
    cL
    fz0
    syl
    feq2d
    cS
    cW
    iswrddm0
    syl6bi
    imp
    pm2.61ian
end
