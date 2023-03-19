include "cmnf.mm"
include "wceq.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "breq2.mm"
include "cxr.mm"
include "wcel.mm"
include "wn.mm"
include "0xr.mm"
include "nltmnf.mm"
include "ax-mp.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "impcom.mm"

theorem xmulasslem2
  let wph: wff ph
  let cA: class A


  assert |- ( ( 0 < A /\ A = -oo ) -> ph )

  proof
    cA
    cmnf
    wceq
    #
    cc0
    cA
    clt
    wbr
    #
    wph
    @0
    @1
    cc0
    cmnf
    clt
    wbr
    #
    wph
    cA
    cmnf
    cc0
    clt
    breq2
    @2
    wph
    cc0
    cxr
    wcel
    @2
    wn
    0xr
    cc0
    nltmnf
    ax-mp
    pm2.21i
    syl6bi
    impcom
end
