include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cv.mm"
include "clcmf.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "ssel.mm"
include "adantr.mm"
include "imp.mm"
include "dvds0.mm"
include "syl.mm"
include "wceq.mm"
include "lcmf0val.mm"
include "ad4ant13.mm"
include "breqtrrd.mm"
include "ralrimiva.mm"
include "wn.mm"
include "cn.mm"
include "crab.mm"
include "wnel.mm"
include "df-nel.mm"
include "lcmfcllem.mm"
include "3expa.mm"
include "sylan2br.mm"
include "wb.mm"
include "lcmfn0cl.mm"
include "breq2.mm"
include "ralbidv.mm"
include "elrab3.mm"
include "mpbid.mm"
include "pm2.61dan.mm"

theorem dvdslcmf
  let vx: setvar x
  let cZ: class Z
  let vn: setvar n

  disjoint Z x
  disjoint Z n
  disjoint n x
  assert |- ( ( Z C_ ZZ /\ Z e. Fin ) -> A. x e. Z x || ( _lcm ` Z ) )

  proof
    cZ
    cz
    wss
    #
    cZ
    cfn
    wcel
    #
    wa
    #
    cc0
    cZ
    wcel
    #
    vx
    cv
    #
    cZ
    clcmf
    cfv
    #
    cdvds
    wbr
    #
    vx
    cZ
    wral
    #
    @2
    @3
    wa
    #
    @6
    vx
    cZ
    @8
    @4
    cZ
    wcel
    #
    wa
    #
    @4
    cc0
    @5
    cdvds
    @10
    @4
    cz
    wcel
    #
    @4
    cc0
    cdvds
    wbr
    @8
    @9
    @11
    @2
    @9
    @11
    wi
    #
    @3
    @0
    @12
    @1
    cZ
    cz
    @4
    ssel
    adantr
    adantr
    imp
    @4
    dvds0
    syl
    @0
    @3
    @5
    cc0
    wceq
    @1
    @9
    cZ
    lcmf0val
    ad4ant13
    breqtrrd
    ralrimiva
    @2
    @3
    wn
    #
    wa
    #
    @5
    @4
    vn
    cv
    #
    cdvds
    wbr
    #
    vx
    cZ
    wral
    #
    vn
    cn
    crab
    wcel
    #
    @7
    @13
    @2
    cc0
    cZ
    wnel
    #
    @18
    cc0
    cZ
    df-nel
    #
    @0
    @1
    @19
    @18
    vx
    vn
    cZ
    lcmfcllem
    3expa
    sylan2br
    @14
    @5
    cn
    wcel
    #
    @18
    @7
    wb
    @13
    @2
    @19
    @21
    @20
    @0
    @1
    @19
    @21
    cZ
    lcmfn0cl
    3expa
    sylan2br
    @17
    @7
    vn
    @5
    cn
    @15
    @5
    wceq
    @16
    @6
    vx
    cZ
    @15
    @5
    @4
    cdvds
    breq2
    ralbidv
    elrab3
    syl
    mpbid
    pm2.61dan
end
